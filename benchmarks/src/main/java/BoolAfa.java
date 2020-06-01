package benchmark;

import static org.typemeta.funcj.parser.Combinators.any;
import static org.typemeta.funcj.parser.Text.intr;
import static org.typemeta.funcj.parser.Text.string;

import java.io.InputStreamReader;
import java.io.Reader;

import org.typemeta.funcj.data.Chr;
import org.typemeta.funcj.parser.Input;
import org.typemeta.funcj.parser.Parser;
import org.typemeta.funcj.tuples.Tuple2;

import benchmark.parser.WhitespaceOmittingReader;

public class BoolAfa {
    public static void main(String[] args) throws InterruptedException {
        Reader in = new WhitespaceOmittingReader(new InputStreamReader(System.in)); 
        Input<Chr> inp = Input.of(in);
        int qcnt_parser = string("QCNT").andR(intr).apply(inp).getOrThrow();
        int acnt_parser = string("ACNT").andR(intr).apply(inp).getOrThrow();
        int scnt_parser = string("SCNT").andR(intr).apply(inp).getOrThrow();
        System.out.println(parser.apply(inp).getOrThrow());
    }
}
