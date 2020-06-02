package utilities;

import java.io.FileReader;
import java.io.FileWriter;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import LTLparser.LTLNode;
import LTLparser.LTLParserProvider;
import automata.safa.BooleanExpressionFactory;
import automata.safa.SAFA;
import automata.safa.booleanexpression.BDDExpression;
import automata.safa.booleanexpression.BDDExpressionFactory;
import ltlconverter.LTLConverter;
import logic.ltl.LTLFormula;
import theory.bdd.BDD;
import theory.bddalgebra.BDDSolver;
import utilities.Pair;
import utilities.Timers;

public class LtlEmptiness {
    static long timeout = 700000;

    static int fromCounter = 0;
    static String emptinessOutputFile = "/tmp/dantoni-emptiness";
    static boolean skipRev = true;
    static boolean useBDDs = true;

    public static void main(String[] args) throws InterruptedException {
        useBDDs = false;
        skipRev = true;
        Path filePath = Paths.get(args[0]);

        try {
            FileWriter fw = new FileWriter(emptinessOutputFile + (useBDDs ? "BDD" : "") + ".csv");
            fw.append("formula, size, total, solver, subsumption, reverse\n");
            try {
                System.out.println(filePath);

                List<LTLNode> nodes = LTLParserProvider.parse(new FileReader(filePath.toFile()));

                int counter = 0;
                for (LTLNode ltl : nodes) {
                    fw.append(filePath.getFileName().toString());
                    System.out.println(counter);
                    if (counter > 0)
                        fw.append(counter + "");
                    fw.append(", ");

                    if (counter >= fromCounter) {
                        Timers.setTimeout(Long.MAX_VALUE);
                        Pair<BDDSolver, LTLFormula<BDD, BDD>> pair = LTLConverter.getLTLBDD(ltl);
                        BDDSolver bdds = pair.first;
                        LTLFormula<BDD, BDD> tot = pair.second.pushNegations(bdds);
                        SAFA<BDD, BDD> safa = tot.getSAFA(bdds);
                        // safa = safa.getUnaryPathSAFA(bdds);

                        fw.append(pair.second.getSize() + ", ");

                        boolean result = true;
                        boolean to1 = false;
                        boolean to2 = false;

                        try {
                            if (useBDDs) {
                                BooleanExpressionFactory<BDDExpression> bef = new BDDExpressionFactory(
                                        safa.stateCount() + 1);
                                result = SAFA.isEquivalent(safa, SAFA.getEmptySAFA(bdds), bdds, bef, timeout)
                                        .getFirst();

                            } else {
                                result = SAFA.isEquivalent(safa, SAFA.getEmptySAFA(bdds), bdds,
                                        SAFA.getBooleanExpressionFactory(), timeout).getFirst();
                            }
                            fw.append(Timers.getFull() + ", " + Timers.getSolver() + ", "
                                    + Timers.getSubsumption() + ", ");
                            System.out.print(Timers.getFull() + ", " + Timers.getSolver() + ", "
                                    + Timers.getSubsumption() + ", " + result + ", ");
                        } catch (TimeoutException toe) {
                            to1 = true;
                            fw.append(timeout + ", " + timeout + ", " + timeout + ", ");
                            System.out.print(timeout + ", " + timeout + ", " + timeout + ", ");
                        }catch (NullPointerException np) {
                            to1 = true;
                            fw.append(timeout + ", " + timeout + ", " + timeout + ", ");
                            System.out.print(timeout + ", " + timeout + ", " + timeout + ", ");
                        }

                        if (!skipRev) {
                            long startTime2 = System.currentTimeMillis();
                            try {
                                boolean result2 = SAFA.areReverseEquivalent(safa, SAFA.getEmptySAFA(bdds), bdds,
                                        timeout);
                                if (!to1 && result != result2)
                                    throw new IllegalArgumentException("bug");
                                fw.append(System.currentTimeMillis() - startTime2 + ", ");
                                System.out.print(System.currentTimeMillis() - startTime2 + ", ");
                            } catch (TimeoutException toe) {
                                fw.append(timeout + ", ");
                                System.out.print(timeout + ", ");
                                to2 = true;
                            }catch (NullPointerException np) {
                                fw.append(timeout + ", ");
                                System.out.print(timeout + ", ");
                                to2 = true;
                            }

                            if (!(to1 && to2)) {
                                fw.append(result + "");
                                System.out.print(result);
                            } else {
                                fw.append("TO");
                                System.out.print("TO");
                            }
                        }

                        fw.append("\n");
                        System.out.println();
                    }
                    counter++;
                }
            } catch (Exception e1) {
                e1.printStackTrace();
            }

            fw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
