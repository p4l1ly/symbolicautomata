package boolafa;

import static org.typemeta.funcj.parser.Text.chr;
import static org.typemeta.funcj.parser.Text.intr;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Optional;
import java.util.stream.Collectors;

import org.apache.commons.collections4.IterableUtils;
import org.sat4j.specs.TimeoutException;
import org.typemeta.funcj.data.Chr;
import org.typemeta.funcj.json.model.JsObject;
import org.typemeta.funcj.json.model.JsValue;
import org.typemeta.funcj.json.parser.JsonParser;
import org.typemeta.funcj.parser.Input;
import org.typemeta.funcj.parser.Parser;
import org.typemeta.funcj.parser.Ref;

import automata.safa.BooleanExpressionFactory;
import automata.safa.SAFA;
import automata.safa.SAFAInputMove;
import automata.safa.booleanexpression.BDDExpression;
import automata.safa.booleanexpression.BDDExpressionFactory;
import automata.safa.booleanexpression.PositiveBooleanExpression;
import automata.safa.booleanexpression.PositiveBooleanExpressionFactory;
import automata.safa.booleanexpression.PositiveBooleanExpressionFactorySimple;
import automata.safa.booleanexpression.PositiveId;
import boolafa.parser.WhitespaceOmittingReader;
import theory.bdd.BDD;
import theory.bddalgebra.BDDSolver;
import theory.sat.SATBooleanAlgebraSimple;

public class BoolAfa {
    static BoolExpr etrue = new True();
    static BoolExpr efalse = new False();
    static Parser<Chr, BoolExpr> expr_parser = get_expr_parser();
    static Parser<Chr, BoolExpr> qexpr_parser = get_qexpr_parser();

    static Parser<Chr, BoolExpr> get_expr_parser() {
        Ref<Chr, BoolExpr> ref_one = Parser.ref();
        Ref<Chr, Collection<BoolExpr>> ref_many = Parser.ref();

        Parser<Chr, BoolExpr> operator_parser = Parser.choice
            ( chr('!').andR(ref_one).map(Not::new)
            , chr('&').andR(ref_many).map(And::new)
            , chr('|').andR(ref_many).map(Or::new)
            );

        Parser<Chr, BoolExpr> expr_parser = Parser.choice
            ( chr('t').map(c -> etrue)
            , chr('f').map(c -> efalse)
            , chr('a').andR(intr).map(Var::new)
            , chr('s').andR(chr('a')).andR(intr).map(ExprRef::new)
            , chr('(').andR(operator_parser).andL(chr(')'))
            );

        ref_one.set(expr_parser);
        ref_many.set(expr_parser.many().map(IterableUtils::toList));

        return expr_parser;
    }

    static Parser<Chr, BoolExpr> get_qexpr_parser() {
        Ref<Chr, Collection<BoolExpr>> ref_many = Parser.ref();

        Parser<Chr, BoolExpr> operator_parser = Parser.choice
            ( chr('&').andR(ref_many).map(And::new)
            , chr('|').andR(ref_many).map(Or::new)
            );

        Parser<Chr, BoolExpr> expr_parser = Parser.choice
            ( chr('t').map(c -> etrue)
            , chr('f').map(c -> efalse)
            , chr('q').andR(intr).map(Var::new)
            , chr('s').andR(chr('q')).andR(intr).map(ExprRef::new)
            , chr('(').andR(operator_parser).andL(chr(')'))
            );

        ref_many.set(expr_parser.many().map(IterableUtils::toList));

        return expr_parser;
    }


    public static void main(String[] args) throws InterruptedException, TimeoutException {
        // parse ////////////////////////////////////////////////////////////////

        int i;
        Reader in = new BufferedReader(new InputStreamReader(System.in));
        JsValue res = JsonParser.parse(in);

        int acnt = res.asObject().get("acnt").asNumber().intValue();

        BoolExpr sq_defs[] = new BoolExpr[res.asObject().get("sqdefs").asArray().size()];
        i = 0;
        for (JsValue x: res.asObject().get("sqdefs").asArray()) {
            Input<Chr> inp = Input.of(new WhitespaceOmittingReader(new StringReader(
                x.asString().value()
            )));
            sq_defs[i] = qexpr_parser.parse(inp).getOrThrow();
            i++;
        }

        BoolExpr sa_defs[] = new BoolExpr[res.asObject().get("sadefs").asArray().size()];
        i = 0;
        for (JsValue x: res.asObject().get("sadefs").asArray()) {
            Input<Chr> inp = Input.of(new WhitespaceOmittingReader(new StringReader(
                x.asString().value()
            )));
            sa_defs[i] = expr_parser.parse(inp).getOrThrow();
            i++;
        }

        int qcnt = res.asObject().get("qdefs").asArray().size();
        ArrayList<ArrayList<QDefPart>>qdefs = new ArrayList<ArrayList<QDefPart>>(qcnt);
        i = 0;
        for (JsValue x: res.asObject().get("qdefs").asArray()) {
            qdefs.add(new ArrayList<QDefPart>());
            for (JsValue y: x.asArray()) {
                JsObject o = y.asObject();
                qdefs.get(i).add(new QDefPart(
                    o.get("post").asNumber().intValue(),
                    o.get("guard").asNumber().intValue()
                ));
            }
            i++;
        }

        // build ////////////////////////////////////////////////////////////////

        PositiveBooleanExpression initialState = new PositiveId(0);
        Collection<Integer> finalStates = new ArrayList<Integer>();

        PositiveBooleanExpressionFactory positive_factory =
            new PositiveBooleanExpressionFactorySimple();

        PositiveBooleanExpression sq_exprs[] =
            new PositiveBooleanExpression[sq_defs.length];
        i = 0;
        for (BoolExpr sq_def: sq_defs) {
            sq_exprs[i] = sq_def.positive(sq_exprs, positive_factory);
            i++;
        }

        Boolean get_symbols_using_bdds =
            Optional.ofNullable(System.getenv("GET_SYMBOLS_USING_BDDS"))
            .orElse("true")
            .equals("true");
        Boolean get_successors_using_bdds =
            Optional.ofNullable(System.getenv("GET_SUCCESSORS_USING_BDDS"))
            .orElse("false")
            .equals("true");

        if (get_symbols_using_bdds) {
            BDDSolver algebra = new BDDSolver(acnt);

            BDD sa_bdds[] = new BDD[sa_defs.length];
            i = 0;
            for (BoolExpr sa_def: sa_defs) {
                sa_bdds[i] = sa_def.bdd(sa_bdds, algebra);
                i++;
            }

            Collection<SAFAInputMove<BDD, BDD>> transitions = new ArrayList<>();
            i = 0;
            for (ArrayList<QDefPart> qdef: qdefs) {
                for (QDefPart qdefpart: qdef) {
                    transitions.add(new SAFAInputMove<BDD, BDD>(
                        i, sq_exprs[qdefpart.post], sa_bdds[qdefpart.guard]
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
            SATBooleanAlgebraSimple algebra = new SATBooleanAlgebraSimple(acnt);

            Integer sa_sat_formulas[] = new Integer[sa_defs.length];
            i = 0;
            for (BoolExpr sa_def: sa_defs) {
                sa_sat_formulas[i] = sa_def.sat_formula(sa_sat_formulas, algebra);
                i++;
            }

            Collection<SAFAInputMove<Integer, boolean[]>> transitions =
                new ArrayList<SAFAInputMove<Integer, boolean[]>>();
            i = 0;
            for (ArrayList<QDefPart> qdef: qdefs) {
                for (QDefPart qdefpart: qdef) {
                    transitions.add(new SAFAInputMove<Integer, boolean[]>(
                        i, sq_exprs[qdefpart.post], sa_sat_formulas[qdefpart.guard]
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

class Counts {
    int qcnt, acnt, sqcnt, sa_cnt;
    public Counts(int qcnt, int acnt, int sqcnt, int sa_cnt) {
        this.qcnt = qcnt;
        this.acnt = acnt;
        this.sqcnt = sqcnt;
        this.sa_cnt = sa_cnt;
    }
}

class QDefPart {
    int post;
    int guard;

    public QDefPart(int post, int guard) {
        this.post = post;
        this.guard = guard;
    }
}

abstract class BoolExpr {
    abstract BDD bdd(BDD bdds[], BDDSolver solver);
    abstract Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra);
    abstract PositiveBooleanExpression positive
        ( PositiveBooleanExpression exprs[]
        , PositiveBooleanExpressionFactory factory
        );
}

class True extends BoolExpr {
    @Override
    BDD bdd(BDD bdds[], BDDSolver solver) {
        return solver.factory.one();
    }

    @Override
    Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra) {
        return algebra.True();
    }

    @Override
    PositiveBooleanExpression positive
    ( PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        return factory.True();
    }
}

class False extends BoolExpr {
    @Override
    BDD bdd(BDD bdds[], BDDSolver solver) {
        return solver.factory.zero();
    }

    @Override
    Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra) {
        return algebra.False();
    }

    @Override
    PositiveBooleanExpression positive
    ( PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        return factory.False();
    }
}

class Var extends BoolExpr {
    public int i;
    public Var(int i) { this.i = i; }

    @Override
    BDD bdd(BDD bdds[], BDDSolver solver) {
        return solver.factory.ithVar(i);
    }

    @Override
    Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra) {
        return i + 1;
    }

    @Override
    PositiveBooleanExpression positive
    ( PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        return factory.MkState(i);
    }
}

class ExprRef extends BoolExpr {
    public int i;
    public ExprRef(int i) { this.i = i; }

    @Override
    BDD bdd(BDD bdds[], BDDSolver solver) {
        return bdds[i];
    }

    @Override
    Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra) {
        return others[i];
    }

    @Override
    PositiveBooleanExpression positive
    ( PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        return exprs[i];
    }
}

class Not extends BoolExpr {
    public BoolExpr operand;
    public Not(BoolExpr operand) { this.operand = operand; }

    @Override
    BDD bdd(BDD bdds[], BDDSolver solver) {
        return solver.MkNot(operand.bdd(bdds, solver));
    }

    @Override
    Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra) {
        return algebra.MkNot(operand.sat_formula(others, algebra));
    }

    @Override
    PositiveBooleanExpression positive
    ( PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        throw new UnsupportedOperationException();
    }
}

class And extends BoolExpr {
    public Collection<BoolExpr> operands;
    public And(Collection<BoolExpr> operands) { this.operands = operands; }

    @Override
    BDD bdd(BDD bdds[], BDDSolver solver) {
        return solver.MkAnd(
            operands.stream()
            .map(x -> x.bdd(bdds, solver))
            .collect(Collectors.toList())
        );
    }

    @Override
    Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra) {
        return algebra.MkAnd(
            operands.stream()
            .map(x -> x.sat_formula(others, algebra))
            .collect(Collectors.toList())
        );
    }

    @Override
    PositiveBooleanExpression positive
    ( PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        return operands.stream()
            .map(x -> x.positive(exprs, factory))
            .reduce((a, b) -> factory.MkAnd(a, b)).get();
    }
}

class Or extends BoolExpr {
    public Collection<BoolExpr> operands;
    public Or(Collection<BoolExpr> operands) { this.operands = operands; }

    @Override
    BDD bdd(BDD bdds[], BDDSolver solver) {
        return solver.MkOr(
            operands.stream()
            .map(x -> x.bdd(bdds, solver))
            .collect(Collectors.toList())
        );
    }

    @Override
    Integer sat_formula(Integer others[], SATBooleanAlgebraSimple algebra) {
        return algebra.MkOr(
            operands.stream()
            .map(x -> x.sat_formula(others, algebra))
            .collect(Collectors.toList())
        );
    }

    @Override
    PositiveBooleanExpression positive
    ( PositiveBooleanExpression exprs[]
    , PositiveBooleanExpressionFactory factory
    ) {
        return operands.stream()
            .map(x -> x.positive(exprs, factory))
            .reduce((a, b) -> factory.MkOr(a, b)).get();
    }
}
