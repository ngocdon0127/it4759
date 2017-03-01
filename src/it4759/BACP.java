package it4759;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Random;

import localsearch.constraints.alldifferent.AllDifferent;
import localsearch.constraints.basic.LessOrEqual;
import localsearch.constraints.basic.LessThan;
import localsearch.functions.basic.ConstraintViolations;
import localsearch.functions.basic.FuncPlus;
import localsearch.functions.conditionalsum.ConditionalSum;
import localsearch.model.ConstraintSystem;
import localsearch.model.IConstraint;
import localsearch.model.IFunction;
import localsearch.model.LocalSearchManager;
import localsearch.model.VarIntLS;
import localsearch.selectors.MinMaxSelector;

public class BACP {
	
	VarIntLS x[]; // solution
	private int n; // number of courses
	private int p; // number of periods
	private int minCredits; // min credits
	private int maxCredits; // max credits
	private int[] credits; // credits
	private int minCourses; // min courses
	private int maxCourses; // max courses
	private int[] courses; // [1, 1, 1, ...]
	private int[][] pre; // Pre...
	private int pres;
	Random r;
	
	LocalSearchManager mgr;
	
	ConstraintSystem cs;
	
	public BACP(String path) throws IOException{
//		this.n = n;
//		x = new VarIntLS[n];
		r = new Random();
		FileInputStream fis = new FileInputStream(path);
		InputStreamReader isr = new InputStreamReader(fis);
		BufferedReader br = new BufferedReader(isr);
		String buf = br.readLine();
		String data[] = buf.split(" "); // n & p
		this.n = Integer.parseInt(data[0]);
		this.p = Integer.parseInt(data[1]);
		credits = new int[n];
		x = new VarIntLS[n];
		
		courses = new int[n];
		for(int i = 0; i < n; i++){
			courses[i] = 1;
		}
		
		buf = br.readLine();
		data = buf.split(" ");
		minCredits = Integer.parseInt(data[0]);
		maxCredits = Integer.parseInt(data[1]);
		
		buf = br.readLine();
		data = buf.split(" ");
		minCourses = Integer.parseInt(data[0]);
		maxCourses = Integer.parseInt(data[1]);
		
		buf = br.readLine();
		data = buf.split(" ");
		if (data.length != n){
			System.out.println("exit");
			System.exit(1);
		}
		for(int i = 0; i < data.length; i++){
			credits[i] = Integer.parseInt(data[i]);
		}
		
		pre = new int[n][n];
		for(int i = 0; i < n; i++){
			for(int j = 0; j < n; j++){
				pre[i][j] = 0;
			}
		}
		
		buf = br.readLine();
		pres = Integer.parseInt(buf);
		for(int i = 0; i < pres; i++){
			buf = br.readLine();
			data = buf.split(" ");
			int cb = Integer.parseInt(data[0]);
			int ca = Integer.parseInt(data[1]);
			pre[cb - 1][ca - 1] = 1;
		}
		
		br.close();
		isr.close();
		fis.close();
	}
	
	
	
	private void init(){
		mgr = new LocalSearchManager();
		for(int i = 0; i < n; i++){
			x[i] = new VarIntLS(mgr, 0, this.p - 1);
			x[i].setValue(r.nextInt(this.p));
		}
		
		cs = new ConstraintSystem(mgr);
		
		
		IFunction[] creditsInPeriods = new IFunction[p];
		IFunction[] coursesInPeriods = new IFunction[p];
		for(int i = 0; i < p; i++){
			creditsInPeriods[i] = new ConditionalSum(x, credits, i);
			IConstraint c1 = new LessOrEqual(creditsInPeriods[i], maxCredits);
			cs.post(c1);
			IConstraint c1_ = new LessOrEqual(minCredits, creditsInPeriods[i]);
			cs.post(c1_);
			
			coursesInPeriods[i] = new ConditionalSum(x, courses, i);
			IConstraint c2 = new LessOrEqual(coursesInPeriods[i], maxCourses);
			cs.post(c2);
			IConstraint c2_ = new LessOrEqual(minCourses, coursesInPeriods[i]);
			cs.post(c2_);
		}
		
		IConstraint[] p_ = new IConstraint[pres];
		int index = 0;
		
		for(int i = 0; i < n; i++){
			for(int j = 0; j < n; j++){
				if (pre[i][j] == 1){
					// course i must be learned before course j
					p_[index] = new LessThan(x[i], x[j]);
					
					cs.post(p_[index]);
					index++;
				}
			}
		}
		
		
		mgr.close();
		
		
	}
	
//	private void solve(){
//		
//	}
	
	public void printResult(){
		for(int i = 0; i < n; i++){
			System.out.println("course " + (i + 1) + " : period " + (x[i].getValue() + 1));
		}
	}
	
	
	

	/**
	 * @param args
	 * @throws IOException
	 */
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BACP nQueens = new BACP("bacp.in06");
		nQueens.init();
//		nQueens.solve();
//		nQueens.hillClimbing();
//		HillClimbingSearch hcs = new HillClimbingSearch(nQueens.cs, 100000);
//		hcs.search();
		TabuSearch ts = new TabuSearch(nQueens.cs, 100000, 20);
		ts.search();
		for(int i = 10; i < 10; i++){
			nQueens = new BACP("bacp.in" + i);
			nQueens.init();
			System.out.println("bacp.in" + i);
//			HillClimbingSearch hcs = new HillClimbingSearch(nQueens.cs, 100000);
//			hcs.search();
			ts = new TabuSearch(nQueens.cs, 100000, 20);
			ts.search();
		}
//		TabuSearch ts = new TabuSearch(nQueens.cs, 100000);
//		ts.search();
//		nQueens.printResult();
		
//		File f = new File("NQueensLib.html");
//		FileOutputStream fos = new FileOutputStream(f);
//		OutputStreamWriter osw = new OutputStreamWriter(fos);
//		BufferedWriter bw = new BufferedWriter(osw);
//		bw.write("<style>table, tr, td{border: 1px solid black;} tr, td{height: 20px} td{width: 20px}</style>\n");
//		bw.write("<table style='border-collapse: collapse'>\n");
//		for(int i = 0; i < nQueens.n; i++){
//			bw.write("<tr>\n");
//			for(int j = 0; j < nQueens.n; j++){
//				if (nQueens.x[i].getValue() == j){
//					bw.write("<td bgcolor='red'></td>\n");
//				}
//				else {
//					bw.write("<td bgcolor='green'></td>\n");
//				}
//			}
//			bw.write("</tr>\n");
//		}
//		bw.write("</table>");
		
//		bw.close();
//		osw.close();
//		fos.close();
	}

}
