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
		while (l < 1000){
			int violations = cs.violations();
			System.out.println(l + " : " + violations);
			if (violations == 0){
				break;
			}
			
			int minDelta = Integer.MAX_VALUE;
			ArrayList list = new ArrayList();
			
			for(int i = 0; i < N * N - 1; i++){
				for(int j = i + 1; j < N * N; j++){
					int row_ = i / N;
					int col_ = i % N;
					int row = j / N;
					int col = j % N;
					
					int delta = cs.getSwapDelta(x[row_][col_], x[row][col]);
					if (delta < minDelta){
						minDelta = delta;
						list.clear();
						list.add(new Position(row_, col_, row, col));
					}
					else if (delta == minDelta){
						list.add(new Position(row_, col_, row, col));
					}
					
				}
			}
			
			if (minDelta < 0){
				Position pos = (Position) list.get(r.nextInt(list.size()));
				int v_ = x[pos.r_][pos.c_].getValue();
				int v = x[pos.r][pos.c].getValue();
				
				x[pos.r_][pos.c_].setValuePropagate(v);
				x[pos.r][pos.c].setValuePropagate(v_);
			}
			else {
//				this.init();
//				for(int i = 0; i < N; i++){
//					if (i % n == 0){
//						System.out.println("");
//					}
//					for(int j = 0; j < N; j++){
//						if (j % n == 0){
//							System.out.print(" ");
//						}
//						System.out.print(x[i][j].getValue() + " ");
//						
//					}
//					System.out.println("");
//					
//				}
//				System.out.println(cs.violations());
//				System.exit(1);
				// random
				int row_ = r.nextInt(N);
				int col_ = r.nextInt(N);
				int row = r.nextInt(N);
				int col = r.nextInt(N);
				int v_ = x[row_][col_].getValue();
				int v = x[row][col].getValue();
				x[row_][col_].setValuePropagate(v);
				x[row][col].setValuePropagate(v_);
			}
			
//			MinMaxSelector mms = new MinMaxSelector(cs);
//			VarIntLS pos = mms.selectMostViolatingVariable();
//			
//			int v_ = pos.getValue();
//			int v = mms.selectMostPromissingValue(pos);
//			if (v_ != v){
////				System.out.println("change from " + pos.getValue() + " to " + v);
////				pos.setValuePropagate(v);
//				int id = pos.getID();
//				
//				int rowIndex_ = map.get(new Integer(id)).intValue() / N;
//				int colIndex_ = map.get(new Integer(id)).intValue() % N;
//				if (row){
//					int colIndex = -1;
//					for(int j = 0; j < N; j++){
//						if (x[rowIndex_][j].getValue() == v){
//							colIndex = j;
//							break;
//						}
//					}
//					if (colIndex != -1){
//						System.out.println("swap in row " + rowIndex_ + " " + colIndex_ + " and " + rowIndex_ + " " + colIndex);
//						System.out.println("before " + x[rowIndex_][colIndex_].getValue() + " " + x[rowIndex_][colIndex].getValue());
//						x[rowIndex_][colIndex_].setValuePropagate(v);
//						x[rowIndex_][colIndex].setValuePropagate(v_);
//						System.out.println("after " + x[rowIndex_][colIndex_].getValue() + " " + x[rowIndex_][colIndex].getValue());
//						
//					}
//					else {
//						System.out.println("wtf searching " + v + " in row " + rowIndex_);
//						for(int i = 0; i < N; i++){
//							for(int j = 0; j < N; j++){
//								System.out.print(x[i][j].getValue() + " ");
//							}
//							System.out.println("");
//						}
//						row = !row;
//					}
//				}
//				else {
//					int rowIndex = -1;
//					for(int i = 0; i < N; i++){
//						if (x[i][colIndex_].getValue() == v){
//							rowIndex = i;
//							break;
//						}
//					}
//					if (rowIndex != -1){
//						System.out.println("swap in col " + rowIndex_ + " " + colIndex_ + " and " + rowIndex + " " + colIndex_);
//						System.out.println("before " + x[rowIndex_][colIndex_].getValue() + " " + x[rowIndex][colIndex_].getValue());
//						x[rowIndex_][colIndex_].setValuePropagate(v);
//						x[rowIndex][colIndex_].setValuePropagate(v_);
//						System.out.println("after " + x[rowIndex_][colIndex_].getValue() + " " + x[rowIndex][colIndex_].getValue());
//					}
//					else {
//						System.out.println("wtf searching " + v + " in col " + colIndex_);
//						for(int i = 0; i < N; i++){
//							for(int j = 0; j < N; j++){
//								System.out.print(x[i][j].getValue() + " ");
//							}
//							System.out.println("");
//						}
//						row = !row;
//					}
//				}
//				
//			}
//			else {
////				this.init();
//				row = !row;
//				System.out.println("skip");
//				System.out.println("\n======================================\n======================================\n");
//				for(int i = 0; i < N; i++){
//					for(int j = 0; j < N; j++){
//						System.out.print(x[i][j].getValue() + " ");
//					}
//					System.out.println("");
//				}
//				int row_ = r.nextInt(N);
//				int col_ = r.nextInt(N);
//				int row = r.nextInt(N);
//				int col = r.nextInt(N);
//				v_ = x[row_][col_].getValue();
//				v = x[row][col].getValue();
//				x[row_][col_].setValuePropagate(v);
//				x[row][col].setValuePropagate(v_);
//			}
			
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

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Sudoku s = new Sudoku();
		s.solve();
//		s.init();
	}

}
