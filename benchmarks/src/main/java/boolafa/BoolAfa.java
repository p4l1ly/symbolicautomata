package boolafa;

import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.sat4j.specs.TimeoutException;
import org.capnproto.StructList;
import org.capnproto.ListList;
import org.capnproto.ReaderArena;
import org.capnproto.ReaderOptions;
import org.capnproto.SegmentReader;

import automata.safa.BooleanExpressionFactory;
import automata.safa.SAFA;
import automata.safa.SAFAInputMove;
import automata.safa.booleanexpression.BDDExpression;
import automata.safa.booleanexpression.BDDExpressionFactory;
import automata.safa.booleanexpression.PositiveBooleanExpression;
import automata.safa.booleanexpression.PositiveBooleanExpressionFactory;
import automata.safa.booleanexpression.PositiveBooleanExpressionFactorySimple;
import automata.safa.booleanexpression.PositiveId;
import automata.safa.BooleanExpression;
import theory.BooleanAlgebra;
import org.automata.safa.capnp.SeparatedAfaSchema.SeparatedAfa;
import org.automata.safa.capnp.SeparatedAfaSchema.QTerm;
import org.automata.safa.capnp.SeparatedAfaSchema.ATerm;
import org.automata.safa.capnp.SeparatedAfaSchema.Conjunct;
import theory.bdd.BDD;
import theory.bddalgebra.BDDSolver;
import theory.sat.SATBooleanAlgebraSimple;

import utilities.Timers;


public class BoolAfa {
    static Boolean GET_SYMBOLS_USING_BDDS =
        Optional.ofNullable(System.getenv("GET_SYMBOLS_USING_BDDS"))
        .orElse("true")
        .equals("true");
    static Boolean GET_SUCCESSORS_USING_BDDS =
        Optional.ofNullable(System.getenv("GET_SUCCESSORS_USING_BDDS"))
        .orElse("false")
        .equals("true");

    ModelChecking solver;

    static PositiveBooleanExpression fromQTerm
    ( QTerm.Reader qterm
    , PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        switch (qterm.which()) {
        case STATE: return factory.MkState(qterm.getState());
        case REF: return exprs[qterm.getRef()];
        case AND: return StreamSupport.stream(qterm.getAnd().spliterator(), false)
            .map(x -> fromQTerm(x, exprs, factory))
            .reduce((a, b) -> factory.MkAnd(a, b)).get();
        case OR: return StreamSupport.stream(qterm.getOr().spliterator(), false)
            .map(x -> fromQTerm(x, exprs, factory))
            .reduce((a, b) -> factory.MkOr(a, b)).get();
        case _NOT_IN_SCHEMA:
            System.err.println("not in schema");
        }
        return factory.True();  // unreachable code
    }

    static Integer sat_formula
    ( ATerm.Reader aterm
    , Integer others[]
    , SATBooleanAlgebraSimple algebra
    ) {
        switch (aterm.which()) {
        case VAR: return aterm.getVar() + 1;
        case REF: return others[aterm.getRef()];
        case NOT: return algebra.MkNot(sat_formula(aterm.getNot(), others, algebra));
        case AND: return algebra.MkAnd(
            StreamSupport.stream(aterm.getAnd().spliterator(), false)
            .map(x -> sat_formula(x, others, algebra))
            .collect(Collectors.toList())
        );
        case OR: return algebra.MkOr(
            StreamSupport.stream(aterm.getOr().spliterator(), false)
            .map(x -> sat_formula(x, others, algebra))
            .collect(Collectors.toList())
        );
        case _NOT_IN_SCHEMA:
            System.err.println("not in schema");
        }
        return algebra.True();  // unreachable code
    }

    static BDD bdd
    ( ATerm.Reader aterm
    , BDD bdds[]
    , BDDSolver solver
    ) {
        switch (aterm.which()) {
        case VAR: return solver.factory.ithVar(aterm.getVar());
        case REF: return bdds[aterm.getRef()];
        case NOT: return solver.MkNot(bdd(aterm.getNot(), bdds, solver));
        case AND: return solver.MkAnd(
            StreamSupport.stream(aterm.getAnd().spliterator(), false)
            .map(x -> bdd(x, bdds, solver))
            .collect(Collectors.toList())
        );
        case OR: return solver.MkOr(
            StreamSupport.stream(aterm.getOr().spliterator(), false)
            .map(x -> bdd(x, bdds, solver))
            .collect(Collectors.toList())
        );
        case _NOT_IN_SCHEMA:
            System.err.println("not in schema");
        }
        return solver.factory.one();
    }

    static {
        System.loadLibrary("boolafaRpc");
    }

    public static void main(String[] args) {
        BoolAfa.runRpcServer();
    }

    private static native void runRpcServer();

    public BoolAfa(
        ByteBuffer[] segments,
        int segment_ix,
        int data_pos,
        int pointer_pos,
        int data_size_bits,
        short pointer_count
    ) {
        for (ByteBuffer seg : segments) {
            seg.order(java.nio.ByteOrder.LITTLE_ENDIAN);
        }

        ReaderOptions options = ReaderOptions.DEFAULT_READER_OPTIONS;
        ReaderArena arena = new ReaderArena(segments, options.traversalLimitInWords);

        SegmentReader segment = arena.tryGetSegment(segment_ix);
        SeparatedAfa.Reader sepafa = SeparatedAfa.factory.constructReader(
            segment, data_pos*8, pointer_pos, data_size_bits, pointer_count,
            options.nestingLimit
        );

        try {
            solver = load(sepafa);
        } catch (TimeoutException e) {
            System.err.println("Timeout loading AFA, this should not happen.");
        }
    }

    public int solve() throws TimeoutException {
        return solver.solve();
    }
    public int pause() { return solver.pause(); }
    public int resume() { return solver.resume(); }
    public int cancel() { return solver.cancel(); }
    public int getStatus() { return solver.getStatus(); }
    public int getTime() { return solver.getTime(); }

    public static ModelChecking load(SeparatedAfa.Reader sepafa) throws TimeoutException {
        int i;
        StructList.Reader<QTerm.Reader> qterms = sepafa.getQterms();
        StructList.Reader<ATerm.Reader> aterms = sepafa.getAterms();
        ListList.Reader<StructList.Reader<Conjunct.Reader>> qdefs = sepafa.getStates();

        int state_count = qdefs.size();

        PositiveBooleanExpression initialState = new PositiveId(0);
        Collection<Integer> finalStates = new ArrayList<Integer>();

        PositiveBooleanExpressionFactory positive_factory =
            new PositiveBooleanExpressionFactorySimple();

        PositiveBooleanExpression sq_exprs[] =
            new PositiveBooleanExpression[qterms.size()];

        PositiveBooleanExpression ptrue = positive_factory.True();

        i = 0;
        for (QTerm.Reader qterm: qterms) {
            sq_exprs[i] = fromQTerm(qterm, sq_exprs, positive_factory);
            i++;
        }

        if (GET_SYMBOLS_USING_BDDS) {
            BDDSolver algebra = new BDDSolver(sepafa.getVariableCount());
            BDD atrue = algebra.factory.one();

            BDD sa_bdds[] = new BDD[aterms.size()];
            i = 0;
            for (ATerm.Reader aterm: aterms) {
                sa_bdds[i] = bdd(aterm, sa_bdds, algebra);
                i++;
            }

            Collection<SAFAInputMove<BDD, BDD>> transitions = new ArrayList<>();
            i = 0;
            for (int j = 0; j < state_count; j++) {
                StructList.Reader<Conjunct.Reader> qdef = qdefs.get(j);
                for (Conjunct.Reader qdefpart: qdef) {
                    int qref = qdefpart.getQterm();
                    int aref = qdefpart.getAterm();
                    transitions.add(new SAFAInputMove<BDD, BDD>(
                        i,
                        qref == -1 ? ptrue : sq_exprs[qref],
                        aref == -1 ? atrue : sa_bdds[aref]
                    ));
                }
                i++;
            }

            SAFA<BDD, BDD> afa = SAFA.MkSAFA(
                transitions, initialState, finalStates, algebra, false, false, false
            );

            if (GET_SUCCESSORS_USING_BDDS) {
                BooleanExpressionFactory<BDDExpression> succ_factory =
                    new BDDExpressionFactory(afa.stateCount() + 1);

                return new ModelChecker<>(afa, algebra, succ_factory);
            }
            else {
                return new ModelChecker<>(
                    afa, algebra, SAFA.getBooleanExpressionFactory());
            }
        }
        else {
            SATBooleanAlgebraSimple algebra = new SATBooleanAlgebraSimple(
                sepafa.getVariableCount()
            );
            Integer atrue = algebra.True();

            Integer sa_sat_formulas[] = new Integer[aterms.size()];
            i = 0;
            for (ATerm.Reader aterm: aterms) {
                sa_sat_formulas[i] = sat_formula(aterm, sa_sat_formulas, algebra);
                i++;
            }

            Collection<SAFAInputMove<Integer, boolean[]>> transitions =
                new ArrayList<SAFAInputMove<Integer, boolean[]>>();
            i = 0;
            for (int j = 0; j < state_count; j++) {
                StructList.Reader<Conjunct.Reader> qdef = qdefs.get(j);
                for (Conjunct.Reader qdefpart: qdef) {
                    int qref = qdefpart.getQterm();
                    int aref = qdefpart.getAterm();
                    transitions.add(new SAFAInputMove<Integer, boolean[]>(
                        i,
                        qref == -1 ? ptrue : sq_exprs[qref],
                        aref == -1 ? atrue : sa_sat_formulas[aref]
                    ));
                }
                i++;
            }

            SAFA<Integer, boolean[]> afa = SAFA.MkSAFA(
                transitions, initialState, finalStates, algebra, false, false, false
            );

            if (GET_SUCCESSORS_USING_BDDS) {
                BooleanExpressionFactory<BDDExpression> succ_factory =
                    new BDDExpressionFactory(afa.stateCount() + 1);
                return new ModelChecker<>(afa, algebra, succ_factory);
            }
            else {
                return new ModelChecker<>(
                    afa, algebra, SAFA.getBooleanExpressionFactory());
            }
        }
    }
}

interface ModelChecking {
    int solve() throws TimeoutException;
    int pause();
    int resume();
    int cancel();
    int getStatus();
    int getTime();
}

class ModelChecker<P, S, E extends BooleanExpression> implements ModelChecking {
    SAFA<P, S> aut, empty;
    BooleanAlgebra<P, S> algebra;
    BooleanExpressionFactory<E> boolexpr;

    SAFA.ControlHandler control;

    public ModelChecker(
        SAFA<P, S> aut,
        BooleanAlgebra<P, S> algebra,
        BooleanExpressionFactory<E> boolexpr
    ) {
        this.aut = aut;
        this.empty = SAFA.getEmptySAFA(algebra);
        this.algebra = algebra;
        this.boolexpr = boolexpr;
        this.control = new SAFA.ControlHandler();
    }

    @Override
    public int solve() throws TimeoutException {
        control.status.set(SAFA.ControlHandler.RUNNING);
        try {
            boolean is_empty = SAFA.isEquivalent(
                aut, empty, algebra, boolexpr, control).getFirst();
            return is_empty ? 0 : 1;
        }
        catch(TimeoutException e) {
            return 2;
        }
    }

    @Override
    public int pause() {
        int old_status = control.status.get();
        if (old_status == SAFA.ControlHandler.RUNNING) {
            control.pauseMutex.lock();
            control.status.set(SAFA.ControlHandler.PAUSED);
            control.runningMutex.lock();
            control.pauseMutex.unlock();
        }
        return old_status;
    }

    @Override
    public int resume() {
        int old_status = control.status.get();
        if (old_status == SAFA.ControlHandler.PAUSED) {
            control.status.set(SAFA.ControlHandler.RUNNING);
            control.runningMutex.unlock();
        }
        return old_status;
    }

    @Override
    public int cancel() {
        int old_status = control.status.get();
        control.status.set(SAFA.ControlHandler.CANCELLED);
        if (old_status == SAFA.ControlHandler.PAUSED) {
            control.runningMutex.unlock();
        }
        return old_status;
    }

    @Override
    public int getStatus() { return control.status.get(); }

    @Override
    public int getTime() { return (int)Timers.getFull(); }
}
