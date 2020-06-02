package boolafa.parser;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.lang.UnsupportedOperationException;

public class WhitespaceOmittingReader extends BufferedReader {
  public WhitespaceOmittingReader(Reader in) {
    super(in);
  }

  @Override
  public int read() throws IOException {
    while(true) {
      int ichr = super.read();
      if (ichr < 0) return ichr;

      char chr = (char)ichr;
      if (!Character.isWhitespace(chr)) {
        return chr;
      }
    }
  }

  @Override
  public int read(char[] cbuf, int off, int len) throws IOException {
    for (int i = 0; i < len; i++) {
      int chr = this.read();
      if (chr < 0) return i;
      cbuf[i + off] = (char)this.read();
    }
    return len;
  }

  @Override
  public String readLine() throws UnsupportedOperationException {
    throw new UnsupportedOperationException();
  }
}
