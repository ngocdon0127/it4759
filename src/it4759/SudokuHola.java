package it4759;

import java.util.Random;

import localsearch.constraints.alldifferent.AllDifferent;
import localsearch.model.ConstraintSystem;
import localsearch.model.LocalSearchManager;
import localsearch.model.VarIntLS;
import localsearch.selectors.MinMaxSelector;

public class SudokuHola {
	LocalSearchManager mgr;
	ConstraintSystem S;
	int N3 = 3;
	int N9 = 9;
	VarIntLS[][] x;
	Random R = new Random();
	
	private void stateModel() {
		mgr = new LocalSearchManager();
		S = new ConstraintSystem(mgr);
		
		x = new VarIntLS[N9][N9];
		
		for(int i = 0; i < N9; i++){
			for (int j = 0; j < N9; j++) {
				x[i][j] = new VarIntLS(mgr, 0, N9-1);
				x[i][j].setValue(j);
			}
			S.post(new AllDifferent(x[i]));
		}
		for(int i = 0; i < N9; i++){
			VarIntLS[] y = new VarIntLS[N9];
			for (int j = 0; j < N9; j++) {
				y[j] = x[j][i];
			}
			S.post(new AllDifferent(y));
		}
		VarIntLS[][] y = new VarIntLS[N9][N9];
		for (int I = 0; I < N3; I++) {
			for(int J = 0; J < N3; J++){
				int k = 0;
				for (int i = 0; i < N9; i++) {
					for (int j = 0; j < N9; j++) {
						if(i/3 == I && j/3 == J){
							y[3*I +J][k++] = x[i][j];
						}
					}
				}
			}
		}
		
		for (int j = 0; j < N9; j++) {
			S.post(new AllDifferent(y[j]));
		}
		mgr.close();
	}
	
	private void search() {
		int it = 0;
		MinMaxSelector mms = new MinMaxSelector(S);
		while(it < 100000 && S.violations() > 0){
			VarIntLS sel_x = mms.selectMostViolatingVariable();
			int chose_x = 0, chose_y = 0; 
			int minViolations = Integer.MAX_VALUE;
			for (int i = 0; i < N9; i++) {
				for (int j = 0; j < N9; j++) {
					if(x[i][j] != sel_x){
						int violations = S.getSwapDelta(sel_x, x[i][j]);
						if (minViolations > violations) {
							minViolations = violations;
							chose_x = i;
							chose_y = j;
						} else if(minViolations == violations){
							chose_x = R.nextInt(N9-1);
							chose_y = R.nextInt(N9-1);
						}
					}
				}
			}
			if (minViolations >= 0){
				System.out.println("eheheee============================");
			}
			int val_v = x[chose_x][chose_y].getValue();
			x[chose_x][chose_y].setValuePropagate(sel_x.getValue());
			sel_x.setValuePropagate(val_v);
			System.out.println("Step: " + it + ", S:" + S.violations());
			it++;
		}
	}
	
	public static void main(String[] args) {
		SudokuHola sudoku = new SudokuHola();
		sudoku.stateModel();
		sudoku.search();
	}
}