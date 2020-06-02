package automata.safa.booleanexpression;

import automata.safa.booleanexpression.PositiveBooleanExpressionFactory;
import utilities.Memo;

public class PositiveBooleanExpressionFactorySimple extends PositiveBooleanExpressionFactory {
	private Memo<Integer,PositiveBooleanExpression> mkState;

	public PositiveBooleanExpressionFactorySimple() {
		mkState = new Memo<Integer,PositiveBooleanExpression>((state) -> new PositiveId(state));
	}

	@Override
	public PositiveBooleanExpression MkAnd(PositiveBooleanExpression phi, PositiveBooleanExpression psi) {
        return new PositiveAnd(phi, psi);
	}
	
	@Override
	public PositiveBooleanExpression MkOr(PositiveBooleanExpression phi, PositiveBooleanExpression psi) {
        return new PositiveOr(phi, psi);
	}

	@Override
	public PositiveBooleanExpression MkState(int state) {
		return mkState.apply(state);
	}

	@Override
	public PositiveBooleanExpression True() {
		return PositiveTrue.getInstance();
	}

	@Override
	public PositiveBooleanExpression False() {
		return PositiveFalse.getInstance();
	}
}

