package boolafa;

import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;
import java.util.Spliterator;
import java.util.function.Consumer;

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
import org.automata.safa.capnp.Afa.Model.Separated;
import org.automata.safa.capnp.Afa.Model.Separated.Conjunct11;
import org.automata.safa.capnp.Afa.Model.Separated.Maybe1;
import org.automata.safa.capnp.Afa.Model.Term;
import theory.bdd.BDD;
import theory.bddalgebra.BDDSolver;
import theory.sat.SATBooleanAlgebraSimple;

import utilities.Timers;


class CapSpliterator implements Spliterator<Integer> {
    org.capnproto.PrimitiveList.Int.Reader reader;
    int ix = 0;

    public CapSpliterator(org.capnproto.PrimitiveList.Int.Reader reader) {
        this.reader = reader;
    }

    @Override
    public int characteristics() {
        return SIZED | NONNULL | IMMUTABLE;
    }

    @Override
    public long estimateSize() {
        return reader.size() - ix;
    }

    @Override
    public Spliterator<Integer> trySplit() {
        return null;
    }

    @Override
    public boolean tryAdvance(Consumer<? super Integer> action) {
        if (ix < reader.size()) {
            action.accept(reader.get(ix));
            ix += 1;
            return true;
        }
        else return false;
    }
}


public class BoolAfaChecking {
    static Boolean GET_SYMBOLS_USING_BDDS =
        Optional.ofNullable(System.getenv("GET_SYMBOLS_USING_BDDS"))
        .orElse("true")
        .equals("true");
    static Boolean GET_SUCCESSORS_USING_BDDS =
        Optional.ofNullable(System.getenv("GET_SUCCESSORS_USING_BDDS"))
        .orElse("false")
        .equals("true");
    static Integer RPC_PORT = Integer.parseInt(
        Optional.ofNullable(System.getenv("RPC_PORT"))
        .orElse("4001")
    );

    ModelChecking solver;

    static PositiveBooleanExpression fromQTerm
    ( Term.QTerm11.Reader qterm
    , PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        switch (qterm.which()) {
        case STATE: return factory.MkState(qterm.getState());
        case AND: return StreamSupport.stream(new CapSpliterator(qterm.getAnd()), false)
            .map(x -> exprs[x])
            .reduce((a, b) -> factory.MkAnd(a, b)).get();
        case OR: return StreamSupport.stream(new CapSpliterator(qterm.getOr()), false)
            .map(x -> exprs[x])
            .reduce((a, b) -> factory.MkOr(a, b)).get();
        case _NOT_IN_SCHEMA:
            System.err.println("not in schema");
        }
        return factory.True();  // unreachable code
    }

    static Integer sat_formula
    ( Term.BoolTerm11.Reader aterm
    , Integer others[]
    , SATBooleanAlgebraSimple algebra
    ) {
        switch (aterm.which()) {
        case PREDICATE: return aterm.getPredicate() + 1;
        case NOT: return algebra.MkNot(others[aterm.getNot()]);
        case AND: return algebra.MkAnd(
            StreamSupport.stream(new CapSpliterator(aterm.getAnd()), false)
            .map(x -> others[x])
            .collect(Collectors.toList())
        );
        case OR: return algebra.MkOr(
            StreamSupport.stream(new CapSpliterator(aterm.getOr()), false)
            .map(x -> others[x])
            .collect(Collectors.toList())
        );
        case _NOT_IN_SCHEMA:
            System.err.println("not in schema");
        }
        return algebra.True();  // unreachable code
    }

    static BDD bdd
    ( Term.BoolTerm11.Reader aterm
    , BDD bdds[]
    , BDDSolver solver
    ) {
        switch (aterm.which()) {
        case PREDICATE: return solver.factory.ithVar(aterm.getPredicate());
        case NOT: return solver.MkNot(bdds[aterm.getNot()]);
        case AND: return solver.MkAnd(
            StreamSupport.stream(new CapSpliterator(aterm.getAnd()), false)
            .map(x -> bdds[x])
            .collect(Collectors.toList())
        );
        case OR: return solver.MkOr(
            StreamSupport.stream(new CapSpliterator(aterm.getOr()), false)
            .map(x -> bdds[x])
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
        System.out.println("Listening on " + RPC_PORT);
        BoolAfaChecking.runRpcServer(RPC_PORT);
    }

    private static native void runRpcServer(int port);

    public BoolAfaChecking(
        ByteBuffer[] segments,
        int segment_ix,
        int data_pos,
        int pointer_pos,
        int data_size_bits,
        short pointer_count
    ) {
        try {
            for (ByteBuffer seg : segments) {
                seg.order(java.nio.ByteOrder.LITTLE_ENDIAN);
            }

            ReaderOptions options = ReaderOptions.DEFAULT_READER_OPTIONS;
            ReaderArena arena = new ReaderArena(segments, options.traversalLimitInWords);

            SegmentReader segment = arena.tryGetSegment(segment_ix);
            Separated.BoolAfa.Reader sepafa = Separated.BoolAfa.factory.constructReader(
                segment, data_pos*8, pointer_pos, data_size_bits, pointer_count,
                options.nestingLimit
            );

            try {
                solver = load(sepafa);
            } catch (TimeoutException e) {
                System.err.println("Timeout loading AFA, this should not happen.");
            }
        } catch(Exception e) {
            e.printStackTrace();
            System.err.println(e);
            System.err.println("Other exception.");
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

    public static ModelChecking load(Separated.BoolAfa.Reader sepafa) throws TimeoutException {
        int i;
        StructList.Reader<Term.QTerm11.Reader> qterms = sepafa.getQterms();
        StructList.Reader<Term.BoolTerm11.Reader> aterms = sepafa.getAterms();
        ListList.Reader<StructList.Reader<Conjunct11.Reader>> qdefs = sepafa.getStates();

        int state_count = qdefs.size();

        PositiveBooleanExpression initialState = new PositiveId(0);
        Collection<Integer> finalStates = new ArrayList<Integer>();

        PositiveBooleanExpressionFactory positive_factory =
            new PositiveBooleanExpressionFactorySimple();

        PositiveBooleanExpression sq_exprs[] =
            new PositiveBooleanExpression[qterms.size()];

        PositiveBooleanExpression ptrue = positive_factory.True();

        i = 0;
        for (Term.QTerm11.Reader qterm: qterms) {
            sq_exprs[i] = fromQTerm(qterm, sq_exprs, positive_factory);
            i++;
        }

        if (GET_SYMBOLS_USING_BDDS) {
            BDDSolver algebra = new BDDSolver(sepafa.getVarCount());
            BDD atrue = algebra.factory.one();

            BDD sa_bdds[] = new BDD[aterms.size()];
            i = 0;
            for (Term.BoolTerm11.Reader aterm: aterms) {
                sa_bdds[i] = bdd(aterm, sa_bdds, algebra);
                i++;
            }

            Collection<SAFAInputMove<BDD, BDD>> transitions = new ArrayList<>();
            i = 0;
            for (int j = 0; j < state_count; j++) {
                StructList.Reader<Conjunct11.Reader> qdef = qdefs.get(j);
                for (Conjunct11.Reader qdefpart: qdef) {
                    Maybe1.Reader qref = qdefpart.getQterm();
                    Maybe1.Reader aref = qdefpart.getAterm();
                    transitions.add(new SAFAInputMove<BDD, BDD>(
                        i,
                        qref.isNothing() ? ptrue : sq_exprs[qref.getJust()],
                        aref.isNothing() ? atrue : sa_bdds[aref.getJust()]
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
                sepafa.getVarCount()
            );
            Integer atrue = algebra.True();

            Integer sa_sat_formulas[] = new Integer[aterms.size()];
            i = 0;
            for (Term.BoolTerm11.Reader aterm: aterms) {
                sa_sat_formulas[i] = sat_formula(aterm, sa_sat_formulas, algebra);
                i++;
            }

            Collection<SAFAInputMove<Integer, boolean[]>> transitions =
                new ArrayList<SAFAInputMove<Integer, boolean[]>>();
            i = 0;
            for (int j = 0; j < state_count; j++) {
                StructList.Reader<Conjunct11.Reader> qdef = qdefs.get(j);
                for (Conjunct11.Reader qdefpart: qdef) {
                    Maybe1.Reader qref = qdefpart.getQterm();
                    Maybe1.Reader aref = qdefpart.getAterm();
                    transitions.add(new SAFAInputMove<Integer, boolean[]>(
                        i,
                        qref.isNothing() ? ptrue : sq_exprs[qref.getJust()],
                        aref.isNothing() ? atrue : sa_sat_formulas[aref.getJust()]
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
