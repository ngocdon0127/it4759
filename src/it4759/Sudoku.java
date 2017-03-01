package it4759;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import it4759.Sudoku.SudokuMove;
import localsearch.constraints.alldifferent.AllDifferent;
import localsearch.model.ConstraintSystem;
import localsearch.model.LocalSearchManager;
import localsearch.model.VarIntLS;
import localsearch.selectors.MinMaxSelector;

public class Sudoku {
	
	VarIntLS x[][];
	Random r;
	LocalSearchManager mgr;
	ConstraintSystem cs;
	
	Map<Integer, Integer> map;
	
	public final int N = 9;
	public final int n = 3;
	
	boolean row = true;
	int tmp = 0;
	int tmp1 = 0;
	
	private void init(){
		r = new Random();
		mgr = new LocalSearchManager();
		cs = new ConstraintSystem(mgr);
		
		x = new VarIntLS[N][N];
		
//		map = new HashMap();
		
		for(int i = 0; i < N; i++){

			
			for(int j = 0; j < N; j++){
				x[i][j] = new VarIntLS(mgr, 0, N - 1);
				x[i][j].setValue(j);
//				int id = x[i][j].getID();

//				map.put(new Integer(id), new Integer(i * N + j));
			}
			cs.post(new AllDifferent(x[i]));
		}
		
		for(int i = 0; i < N; i++){
			VarIntLS[] y = new VarIntLS[N];

			for(int j = 0; j < N; j++){
				y[j] = x[j][i];

			}
			cs.post(new AllDifferent(y));

		}
		
		for(int i = 0; i < n; i++){
			for(int j = 0; j < n; j++){
				VarIntLS[] y = new VarIntLS[N];
				
				for(int k = 0; k < N; k++){
					y[k] = x[i * n + k / n][j * n + k % n];
				}
				cs.post(new AllDifferent(y));
			}
		}
		
		
		
		mgr.close();
	}
	
	private void solve(){
		int l = 0;
//		MinMaxSelector mms = new MinMaxSelector(cs);
		while (l < 100000){
			int violations = cs.violations();
			
			System.out.println(l + " : " + violations);

			if (violations == 0){
				System.out.println("done");
				break;
			}
			
			
			ArrayList<SudokuMove> list = new ArrayList<SudokuMove>();
			
			
			int mDelta = Integer.MAX_VALUE;

			for (int i = 0; i < N; i++) {
				for(int j1 = 0; j1 < N - 1; j1++){
					for(int j2 = j1 + 1; j2 < N; j2++){
						int delta = cs.getSwapDelta(x[i][j1], x[i][j2]);
						if (delta < mDelta){
							mDelta = delta;
							list.clear();
							list.add(new SudokuMove(i, j1, i, j2));
						}
						else if (delta == mDelta){
							list.add(new SudokuMove(i, j1, i, j2));
						}
					}
				}
			}

			if (mDelta < 0){
				SudokuMove p = (SudokuMove) list.get(r.nextInt(list.size()));
				x[p.r_][p.c_].swapValuePropagate(x[p.r][p.c]);
				
			}
			
			else {
				tmp++;
				int row_ = r.nextInt(N);
				int col_ = r.nextInt(N);
//				int row = r.nextInt(N);
				int col = r.nextInt(N);
				x[row_][col_].swapValuePropagate(x[row_][col]);
			}

//			System.out.println(l + " : " + violations + " tmp " + tmp + " tmp1 " + tmp1);
			l++;
			
		}
	}
	
	class SudokuMove{
		int r_;
		int r;
		int c;
		int c_;
		
		public SudokuMove(int r_, int c_, int r, int c){
			this.r_ = r_;
			this.r = r;
			this.c_ = c_;
			this.c = c;
		}
		
	}

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Sudoku s = new Sudoku();
		s.init();
		s.solve();
//		System.out.println("tmp: " + s.tmp + " tmp1: " + s.tmp1++);
	}

}
