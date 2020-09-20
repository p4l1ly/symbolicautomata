package boolafa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.sat4j.specs.TimeoutException;
import org.capnproto.StructList;
import org.capnproto.ListList;

import automata.safa.BooleanExpressionFactory;
import automata.safa.SAFA;
import automata.safa.SAFAInputMove;
import automata.safa.booleanexpression.BDDExpression;
import automata.safa.booleanexpression.BDDExpressionFactory;
import automata.safa.booleanexpression.PositiveBooleanExpression;
import automata.safa.booleanexpression.PositiveBooleanExpressionFactory;
import automata.safa.booleanexpression.PositiveBooleanExpressionFactorySimple;
import automata.safa.booleanexpression.PositiveId;
import org.automata.safa.capnp.SeparatedAfaSchema.SeparatedAfa;
import org.automata.safa.capnp.SeparatedAfaSchema.QTerm;
import org.automata.safa.capnp.SeparatedAfaSchema.ATerm;
import org.automata.safa.capnp.SeparatedAfaSchema.Conjunct;
import theory.bdd.BDD;
import theory.bddalgebra.BDDSolver;
import theory.sat.SATBooleanAlgebraSimple;


public class BoolAfa {
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
        }
        return solver.factory.one();
    }


    public static void main(String[] args)
    throws InterruptedException, TimeoutException, java.io.IOException {
        // env //////////////////////////////////////////////////////////////////
        Boolean get_symbols_using_bdds =
            Optional.ofNullable(System.getenv("GET_SYMBOLS_USING_BDDS"))
            .orElse("true")
            .equals("true");
        Boolean get_successors_using_bdds =
            Optional.ofNullable(System.getenv("GET_SUCCESSORS_USING_BDDS"))
            .orElse("false")
            .equals("true");


        // build ////////////////////////////////////////////////////////////////
        int i;

        org.capnproto.MessageReader message =
            org.capnproto.SerializePacked.readFromUnbuffered(
                (new java.io.FileInputStream(java.io.FileDescriptor.in)).getChannel()
            );

        SeparatedAfa.Reader sepafa = message.getRoot(SeparatedAfa.factory);
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

        if (get_symbols_using_bdds) {
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

            // run //////////////////////////////////////////////////////////////////

            Boolean is_empty;

            if (get_successors_using_bdds) {
                BooleanExpressionFactory<BDDExpression> succ_factory =
                    new BDDExpressionFactory(afa.stateCount() + 1);
                is_empty = SAFA.isEquivalent
                    ( afa
                    , SAFA.getEmptySAFA(algebra)
                    , algebra
                    , succ_factory
                    , 60000
                    ).getFirst();
            }
            else {
                is_empty = SAFA.isEquivalent
                    ( afa
                    , SAFA.getEmptySAFA(algebra)
                    , algebra
                    , SAFA.getBooleanExpressionFactory()
                    , 60000
                    ).getFirst();
            }

            System.out.println(is_empty ? "empty" : "nonempty");
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

            // run //////////////////////////////////////////////////////////////////

            Boolean is_empty;

            if (get_successors_using_bdds) {
                BooleanExpressionFactory<BDDExpression> succ_factory =
                    new BDDExpressionFactory(afa.stateCount() + 1);
                is_empty = SAFA.isEquivalent
                    ( afa
                    , SAFA.getEmptySAFA(algebra)
                    , algebra
                    , succ_factory
                    , 60000
                    ).getFirst();
            }
            else {
                is_empty = SAFA.isEquivalent
                    ( afa
                    , SAFA.getEmptySAFA(algebra)
                    , algebra
                    , SAFA.getBooleanExpressionFactory()
                    , 60000
                    ).getFirst();
            }

            System.out.println(is_empty ? "empty" : "nonempty");
        }
    }
}
