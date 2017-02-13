package it4759;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

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
	
	public Sudoku(){
		
	}
	
	private void init(){
		
		r = new Random();
		
		if (mgr != null){
			mgr = null;
			System.gc();
		}
		
		
		mgr = new LocalSearchManager();
		
		if (cs != null){
			cs = null;
			System.gc();
		}
		
		cs = new ConstraintSystem(mgr);
		
		if (x != null){
			x = null;
			System.gc();
		}
		
		x = new VarIntLS[N][N];
		
		map = new HashMap();
		
		for(int i = 0; i < N; i++){
//			x[i] = new VarIntLS[N];
			
			for(int j = 0; j < N; j++){
				x[i][j] = new VarIntLS(mgr, 0, N - 1);
//				x[i][j].setValue(r.nextInt(N));
				x[i][j].setValue(j);
				int id = x[i][j].getID();
//				System.out.println(i + " " + j + " : " + id);
				map.put(new Integer(id), new Integer(i * N + j));
			}
//			cs.post(new AllDifferent(x[i]));
		}
		
		for(int i = 0; i < N; i++){
			VarIntLS[] y = new VarIntLS[N];
			VarIntLS[] y1 = new VarIntLS[N];
			for(int j = 0; j < N; j++){
				y[j] = x[j][i];
				y1[j] = x[i][j];
			}
			cs.post(new AllDifferent(y));
			cs.post(new AllDifferent(y1));
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
		this.init();
		int l = 0;
		MinMaxSelector mms = new MinMaxSelector(cs);
		while (l < 100000){
			int violations = cs.violations();

			if (violations == 0){
				System.out.println("done");
				break;
			}
			
			int mDelta = Integer.MAX_VALUE;

			VarIntLS sel_x = mms.selectMostViolatingVariable();
			
			ArrayList l_ = new ArrayList();
			
			for(int i = 0; i < N; i++){
				for(int j = 0; j < N; j++){
					if (sel_x != x[i][j]){
						int delta = cs.getSwapDelta(sel_x, x[i][j]);
						if (delta < mDelta){
							mDelta = delta;
							l_.clear();
							l_.add(new Point(i, j));
						}
						else if (delta == mDelta){
//							l_.clear();
							l_.add(new Point(i, j));
//							l_.add(new Point(r.nextInt(N), r.nextInt(N)));
						}
					}
				}
			}
			
			System.out.println(l + " : " + violations + " mDelta " + mDelta + " list size " + l_.size());
			
			if (mDelta < 0){
				Point p = (Point) l_.get(r.nextInt(l_.size()));
				
				int v = sel_x.getValue();
				sel_x.setValuePropagate(x[p.r][p.c].getValue());
				x[p.r][p.c].setValuePropagate(v);
			}
			else {
				tmp++;
				
//				Point p = (Point) l_.get(r.nextInt(l_.size()));
//				
//				int v = sel_x.getValue();
//				sel_x.setValuePropagate(x[p.r][p.c].getValue());
//				x[p.r][p.c].setValuePropagate(v);
				
				int row_ = r.nextInt(N);
				int col_ = r.nextInt(N);
				int row = r.nextInt(N);
				int col = r.nextInt(N);
				int v_ = x[row_][col_].getValue();
				int v = x[row][col].getValue();
				x[row_][col_].setValuePropagate(v);
				x[row][col].setValuePropagate(v_);
				
//				continue;
//				int minDelta = Integer.MAX_VALUE;
//				ArrayList list = new ArrayList();
//				
//				for(int i = 0; i < N * N - 1; i++){
//					for(int j = i + 1; j < N * N; j++){
//						int row_ = i / N;
//						int col_ = i % N;
//						int row = j / N;
//						int col = j % N;
//						
//						int delta = cs.getSwapDelta(x[row_][col_], x[row][col]);
//						if (delta < minDelta){
//							minDelta = delta;
//							list.clear();
//							list.add(new Position(row_, col_, row, col));
//						}
//						else if (delta == minDelta){
//							list.add(new Position(row_, col_, row, col));
//						}
//						
//					}
//				}
//				
//				if (minDelta < 0){
//					tmp1++;
//					Position pos = (Position) list.get(r.nextInt(list.size()));
//					int v_ = x[pos.r_][pos.c_].getValue();
//					int v = x[pos.r][pos.c].getValue();
//					
//					x[pos.r_][pos.c_].setValuePropagate(v);
//					x[pos.r][pos.c].setValuePropagate(v_);
//				}
//				else {
//					
//					int row_ = r.nextInt(N);
//					int col_ = r.nextInt(N);
//					int row = r.nextInt(N);
//					int col = r.nextInt(N);
//					int v_ = x[row_][col_].getValue();
//					int v = x[row][col].getValue();
//					x[row_][col_].setValuePropagate(v);
//					x[row][col].setValuePropagate(v_);
//					
//				}
				
				
			}
			
			
			
			
			
			
			
			l++;
			
		}
	}
	
	class Position{
		int r_;
		int r;
		int c;
		int c_;
		
		public Position(int r_, int c_, int r, int c){
			this.r_ = r_;
			this.r = r;
			this.c_ = c_;
			this.c = c;
		}
		
	}
	
	class Point{
		int r;
		int c;
		
		public Point(int r, int c){
			this.r = r;
			this.c = c;
		}
	}

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Sudoku s = new Sudoku();
		s.solve();
		System.out.println("tmp: " + s.tmp + " tmp1: " + s.tmp1++);
//		s.init();
	}

}
