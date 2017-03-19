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
import localsearch.functions.basic.FuncMinus;
import localsearch.functions.basic.FuncPlus;
import localsearch.functions.conditionalsum.ConditionalSum;
import localsearch.functions.conditionalsum.ConditionalSumTmp;
import localsearch.functions.max_min.Max;
import localsearch.functions.max_min.Min;
import localsearch.functions.sum.Sum;
import localsearch.model.ConstraintSystem;
import localsearch.model.IConstraint;
import localsearch.model.IFunction;
import localsearch.model.LocalSearchManager;
import localsearch.model.VarIntLS;
import localsearch.selectors.MinMaxSelector;

public class PPS {
	
	
	Random r;
	VarIntLS[][] x; // solution
	int nBoats; 
	int nPeriods;
	int nGuests;
	int s[]; // Size of Guests
	int c[]; // Capacity
	
	LocalSearchManager mgr;
	
	ConstraintSystem cs;
	
	public PPS(String path) throws IOException{
//		this.n = n;
//		x = new VarIntLS[n];
		r = new Random();
		FileInputStream fis = new FileInputStream(path);
		InputStreamReader isr = new InputStreamReader(fis);
		BufferedReader br = new BufferedReader(isr);
		String buf = br.readLine(); // Skip the first line
		buf = br.readLine();
		String data[] = buf.split(" "); // nGuests, bBoats, bPeriods;
		this.nGuests = Integer.parseInt(data[0]);
		this.nBoats = Integer.parseInt(data[1]);
		this.nPeriods = Integer.parseInt(data[2]);
//		System.out.println(nGuests + " " + nBoats + " " + nPeriods);
		
		
		
		buf = br.readLine(); // skip some labels
		
		c = new int[nBoats];
		for(int i = 0; i < nBoats; i++){
			buf = br.readLine();
			data = buf.split(" ");
			c[i] = Integer.parseInt(data[1]);
//			System.out.println(i + " : " + c[i]);
		}
		
		buf = br.readLine(); // skip some labels
		
		s = new int[nGuests];
		for(int i = 0; i < nGuests; i++){
			buf = br.readLine();
			data = buf.split(" ");
			s[i] = Integer.parseInt(data[1]);
		}
				

//		
		br.close();
		isr.close();
		fis.close();
	}
	
	
	
	private void init(){
		mgr = new LocalSearchManager();
		
		cs = new ConstraintSystem(mgr);
		
		// init x
		x = new VarIntLS[nPeriods][nGuests];
		for(int i = 0; i < nPeriods; i++){
			for(int j = 0; j < nGuests; j++){
				x[i][j] = new VarIntLS(mgr, 0, nBoats - 1);
				x[i][j].setValue(r.nextInt(this.nBoats));
			}
		}
		
		
//		
		for(int i = 0; i < nGuests; i++){
			VarIntLS[] y = new VarIntLS[nPeriods];
			for(int j = 0; j < nPeriods; j++){
				y[j] = x[j][i];
			}
			cs.post(new AllDifferent(y));
			
		}
		
		
		for(int i = 0; i < nGuests - 1; i++){
			for(int j = i + 1; j < nGuests; j++){
				IFunction[] f = new IFunction[nPeriods];
				int[] w = new int[nPeriods];
				for(int k = 0; k < nPeriods; k++){
					w[k] = 1;
					
//					f[k] = new FuncMinus(x[k][i], x[k][j]); // f[k] with negative value will cause the program crash. Don't know why
					VarIntLS[] y_ = new VarIntLS[2];
					y_[0] = x[k][i];
					y_[1] = x[k][j];
					IFunction min_ = new Min(y_);
					IFunction max_ = new Max(y_);
					
					f[k] = new FuncMinus(max_, min_);
				}
				IFunction f_ = new ConditionalSumTmp(f, w, 0);
				cs.post(new LessOrEqual(f_, 1));
			}
		}
		
		for(int k = 0; k < nBoats; k++){
			for(int j = 0; j < nPeriods; j++){
				VarIntLS[] y = new VarIntLS[nGuests];
				for(int i = 0; i < nGuests; i++){
					y[i] = x[j][i];
				}
				IFunction f = new ConditionalSum(y, s, k);
				cs.post(new LessOrEqual(f, c[k]));
			}
			
		}
		
		mgr.close();
		
		
	}
	
//	private void solve(){
//		
//	}
	
	public void printResult() throws IOException{
		File f = new File("PPS.txt");
		FileOutputStream fos = new FileOutputStream(f);
		OutputStreamWriter osw = new OutputStreamWriter(fos);
		BufferedWriter bw = new BufferedWriter(osw);

		

		for(int i = 0; i < nPeriods; i++){
			bw.write("========= Periods " + i + ": ==========\n");
			for(int j = 0; j < nBoats; j++){
				bw.write("boat " + j + ": ");
				for(int k = 0; k < nGuests; k++){
					if (x[i][k].getValue() == j){
						bw.write(k + " ");
					}
					
				}
				bw.write("\n");
			}
		}
		
		bw.write("\n\n");
		bw.write("Constraint 1: Each guest must visit at least one boat for each day\n");
		bw.write("Passed!\n\n");
		
		bw.write("Constraint 2: No boat can host more people than its capacity\n");
		int[][] c1 = new int[nBoats][nPeriods];
		for(int i = 0; i < nBoats; i++){
			for(int j = 0; j < nPeriods; j++){
				c1[i][j] = 0;
			}
		}
		
		boolean constraint1 = true;
		for(int i = 0; i < nBoats; i++){
			bw.write("========== Boat " + i + ":\n");
			int overload = 0;
			for(int j = 0; j < nPeriods; j++){
				int sum = 0;
				for(int k = 0; k < nGuests; k++){
					if (x[j][k].getValue() == i){
						sum += s[k];
					}
				}
				bw.write("\tPeriod " + j + ": " + sum + "/" + c[i] + "");
				if (sum > c[i]){
					bw.write("Failed.");
					overload++;
					constraint1 = false;
				}
				bw.write("\n");
			}
			bw.write("Boat " + i + ": Overload " + overload + "\n");
		}
		
		if (constraint1){
			bw.write("Passed!\n\n");
		}
		else {
			bw.write("Failed!\n\n");
		}
		
		bw.write("Constraint 3: Each guest visit a boat at most once\n");
		int[][] c3 = new int[nGuests][nBoats];
		
		for(int i = 0; i < nGuests; i++){
			for(int j = 0; j < nBoats; j++){
				for(int k = 0; k < nPeriods; k++){
					if (x[k][i].getValue() == j){
						c3[i][j]++;
					}
				}
			}
		}
		boolean constraint3 = true;
		for(int i = 0; i < nGuests; i++){
			for(int j = 0; j < nBoats; j++){
				bw.write(c3[i][j] + " ");
				if (c3[i][j] > 1){
					constraint3 = false;
				}
			}
			bw.write("\n");
		}
		
		if (constraint3){
			bw.write("Passed!\n\n");
		}
		else {
			bw.write("Failed!\n\n");
		}
		
		bw.write("Constraint 4: No two guests meet each other more than once\n");
		int[][] c4 = new int[nGuests][nGuests];
		for(int i = 0; i < nGuests; i++){
			for(int j = 0; j < nGuests; j++){
				c4[i][j] = 0;
			}
		}
		
		for(int i = 0; i < nGuests - 1; i++){
			for(int j = i + 1; j < nGuests; j++){
				for(int k = 0; k < nPeriods; k++){
					if (x[k][i].getValue() == x[k][j].getValue()){
						c4[i][j]++;
						c4[j][i]++;
					}
				}
			}
		}
		boolean constraint4 = true;
		for(int i = 0; i < nGuests; i++){
			for(int j = 0; j < nGuests; j++){
				bw.write(c4[i][j] + " ");
				if (c4[i][j] > 1){
					constraint4 = false;
				}
			}
			bw.write("\n");
		}
		
		if (constraint3){
			bw.write("Passed!\n\n");
		}
		else {
			bw.write("Failed!\n\n");
		}
		
		bw.close();
		osw.close();
		fos.close();
	}
	
	
	

	/**
	 * @param args
	 * @throws IOException
	 */
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		PPS nQueens = new PPS("progressive-party-std.txt");
		nQueens.init();
//		nQueens.solve();
//		nQueens.hillClimbing();
		HillClimbingSearch hcs = new HillClimbingSearch(nQueens.cs, 100000);
		hcs.search();
//		TabuSearch ts = new TabuSearch(nQueens.cs, 100000, 20);
//		ts.search();
//		for(int i = 10; i < 10; i++){
//			nQueens = new PPS("bacp.in" + i);
//			nQueens.init();
//			System.out.println("bacp.in" + i);
////			HillClimbingSearch hcs = new HillClimbingSearch(nQueens.cs, 100000);
////			hcs.search();
//			ts = new TabuSearch(nQueens.cs, 100000, 20);
//			ts.search();
//		}
//		TabuSearch ts = new TabuSearch(nQueens.cs, 100000);
//		ts.search();
		nQueens.printResult();
		
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
