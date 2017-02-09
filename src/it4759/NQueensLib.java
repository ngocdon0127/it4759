package it4759;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Random;

import localsearch.constraints.alldifferent.AllDifferent;
import localsearch.functions.basic.ConstraintViolations;
import localsearch.functions.basic.FuncPlus;
import localsearch.model.ConstraintSystem;
import localsearch.model.IConstraint;
import localsearch.model.IFunction;
import localsearch.model.LocalSearchManager;
import localsearch.model.VarIntLS;
import localsearch.selectors.MinMaxSelector;

public class NQueensLib {
	
	VarIntLS x[];
	private int n;
	Random r;
	
	LocalSearchManager mgr;
	
	ConstraintSystem cs;
	
	public NQueensLib(int n){
		this.n = n;
		x = new VarIntLS[n];
		r = new Random();
	}
	
	
	
	private void init(){
		mgr = new LocalSearchManager();
		for(int i = 0; i < n; i++){
			x[i] = new VarIntLS(mgr, 0, this.n - 1);
			x[i].setValue(r.nextInt(this.n));
		}
		
		cs = new ConstraintSystem(mgr);
		IConstraint f1 = new AllDifferent(x);
		cs.post(f1);
		
		IFunction f2[] = new IFunction[this.n];
		for(int i = 0; i < this.n; i++){
			f2[i] = new FuncPlus(x[i], i);
		}
		
		cs.post(new AllDifferent(f2));
		
		IFunction f3[] = new IFunction[this.n];
		
		for(int i = 0; i < this.n; i++){
			f3[i] = new FuncPlus(x[i], -i);
		}
		
		cs.post(new AllDifferent(f3));
		
		
		mgr.close();
		
		
	}
	
	
	
	private void solve(){
		this.init();
		int l = 0;
		while (l < 10000){
			int totalConflicts = cs.violations();
			System.out.println(l + " : " + totalConflicts);
			if (totalConflicts == 0){
				break;
			}
			
			MinMaxSelector mms = new MinMaxSelector(cs);
			VarIntLS x_ = mms.selectMostViolatingVariable();
			x_.setValuePropagate(mms.selectMostPromissingValue(x_));
			l++;
		}
	}
	
	class Move{
		public int v;
		public int i;
		public Move(int v, int i){
			this.v = v;
			this.i = i;
		}
	}
	
	private void hillClimbing(){
		this.init();
		
		int l = 0;
		ArrayList<Move> list = new ArrayList<Move>();
		
		while (l < 10000){
			int totalConflicts = cs.violations();
			System.out.println(l + " : " + totalConflicts);
			if (totalConflicts == 0){
				break;
			}
			
			int minDelta = Integer.MAX_VALUE;
			list.clear();
			for(int i = 0; i < this.n; i++){
//				minDelta = Integer.MAX_VALUE;
				for(int j = 0; j < this.n; j++){
					if (j != x[i].getValue()){
						int delta = cs.getAssignDelta(x[i], j);
						if (delta < minDelta){
							System.out.println("setting delta from " + minDelta + " to " + delta);
							minDelta = delta;
							list.clear();
							list.add(new Move(i, j));
						}
						else if (delta == minDelta){
							list.add(new Move(i, j));
						}
					}
				}
			}
			System.out.println(l + " : minDelta : " + minDelta);
			if (minDelta >= 0){
				this.init();
				System.out.println("restart");
				
			}
			else {
				Move m = list.get(r.nextInt(list.size()));
				System.out.println(list.size() + " moving: " + m.i + " from " + x[m.i].getValue() + " => " + m.v);
				x[m.i].setValuePropagate(m.v);
			}
			
			l++;
			
		}
		
	}

	/**
	 * @param args
	 * @throws IOException
	 */
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		NQueensLib nQueens = new NQueensLib(10);
//		nQueens.solve();
		nQueens.hillClimbing();
		File f = new File("NQueensLib.html");
		FileOutputStream fos = new FileOutputStream(f);
		OutputStreamWriter osw = new OutputStreamWriter(fos);
		BufferedWriter bw = new BufferedWriter(osw);
		bw.write("<style>table, tr, td{border: 1px solid black;} tr, td{height: 20px} td{width: 20px}</style>\n");
		bw.write("<table style='border-collapse: collapse'>\n");
		for(int i = 0; i < nQueens.n; i++){
			bw.write("<tr>\n");
			for(int j = 0; j < nQueens.n; j++){
				if (nQueens.x[i].getValue() == j){
					bw.write("<td bgcolor='red'></td>\n");
				}
				else {
					bw.write("<td bgcolor='green'></td>\n");
				}
			}
			bw.write("</tr>\n");
		}
		bw.write("</table>");
		
		bw.close();
		osw.close();
		fos.close();
	}

}
