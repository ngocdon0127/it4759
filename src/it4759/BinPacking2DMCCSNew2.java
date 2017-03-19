package it4759;

import localsearch.constraints.basic.*;
import localsearch.functions.basic.FuncPlus;
import localsearch.model.ConstraintSystem;
import localsearch.model.IConstraint;
import localsearch.model.LocalSearchManager;
import localsearch.model.VarIntLS;
import localsearch.search.TabuSearch;
import it4759.HillClimbingSearch.HCMove;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Random;
import java.util.Scanner;


public class BinPacking2DMCCSNew2 {
	public int m;
	public int[] W;
	public int[] H;
	
	public int n;
	public int[] w;
	public int[] h;
	
	int maxW = -1;
	int maxH = -1;
	Random r;

	
	LocalSearchManager ls;
	ConstraintSystem S;
	VarIntLS[] containerOf; // item i belongs to container containerOf[i]. i = (0 => n - 1)
	VarIntLS[] x;
	VarIntLS[] y;
	VarIntLS[] o;
	
	int[] rx;
	int[] ry;
	int[] ro;
	int[] rc;
	int minViolations;

	public BinPacking2DMCCSNew2() {
		r = new Random();
	}

	public void readData(String fn) {
		try {
//			Scanner in = new Scanner(new File(fn));
//			W = in.nextInt();
//			H = in.nextInt();
			FileInputStream fis = new FileInputStream(fn);
			InputStreamReader isr = new InputStreamReader(fis);
			BufferedReader br = new BufferedReader(isr);
			String buf = br.readLine(); 
			m = Integer.parseInt(buf.split(" ")[0]);
			n = Integer.parseInt(buf.split(" ")[1]);
			W = new int[m];
			H = new int[m];
			w = new int[n];
			h = new int[n];
			rx = new int[n];
			ry = new int[n];
			ro = new int[n];
			rc = new int[n];
			minViolations = Integer.MAX_VALUE;
			for(int i = 0; i < m; i++){
				buf = br.readLine();
				W[i] = Integer.parseInt(buf.split(" ")[0]);
				H[i] = Integer.parseInt(buf.split(" ")[1]);
				maxW = (maxW < W[i]) ? W[i] : maxW;
				maxH = (maxH < H[i]) ? H[i] : maxH;
			}
			ArrayList<Item> I = new ArrayList<Item>();
			for(int i = 0; i < n; i++){
				buf = br.readLine();
				w[i] = Integer.parseInt(buf.split(" ")[0]);
				h[i] = Integer.parseInt(buf.split(" ")[1]);
				I.add(new Item(w[i], h[i]));
			}
			br.close();
			isr.close();
			fis.close();
			System.out.println("m = " + m + " n = " + n);
			for(int i = 0; i < m; i++){
				System.out.println("container " + i + ": " + W[i] + " " + H[i]);
			}
			for(int i = 0; i < n; i++){
				System.out.println("item " + i + ": " + w[i] + " " + h[i]);
			}
		} catch (Exception ex) {
			ex.printStackTrace();
		}
	}

	public void stateModel() {
		ls = new LocalSearchManager();
		S = new ConstraintSystem(ls);
		containerOf = new VarIntLS[n];
		x = new VarIntLS[n];
		y = new VarIntLS[n];
		o = new VarIntLS[n];
		
		for (int i = 0; i < n; i++) {
			x[i] = new VarIntLS(ls, 0, maxW);
			y[i] = new VarIntLS(ls, 0, maxH);
			o[i] = new VarIntLS(ls, 0, 1);
			containerOf[i] = new VarIntLS(ls, 0, m - 1);
		}
		
		for(int i = 0; i < n; i++){
			x[i].setValue(r.nextInt(maxW + 1));
			y[i].setValue(r.nextInt(maxH + 1));
			o[i].setValue(r.nextInt(2));
			containerOf[i].setValue(r.nextInt(m));
		}

		
		for(int ic = 0; ic < m; ic++){
			// item i is inside container ic
			for (int i = 0; i < n; i++) {
				IConstraint c_ = new IsEqual(containerOf[i], ic);
				S.post(new Implicate(new AND(new IsEqual(o[i], 0), c_), new LessOrEqual(
						new FuncPlus(x[i], w[i]), W[ic])));
				S.post(new Implicate(new AND(new IsEqual(o[i], 0), c_), new LessOrEqual(
						new FuncPlus(y[i], h[i]), H[ic])));
				S.post(new Implicate(new AND(new IsEqual(o[i], 1), c_), new LessOrEqual(
						new FuncPlus(x[i], h[i]), W[ic])));
				S.post(new Implicate(new AND(new IsEqual(o[i], 1), c_), new LessOrEqual(
						new FuncPlus(y[i], w[i]), H[ic])));
			}
		}

		for(int ic = 0; ic < m; ic++){
			// 2 items in 1 container is not overlapped
			for (int i = 0; i < n - 1; i++) {
				for (int j = i + 1; j < n; j++) {
					// o[i] = 0, o[j] = 0 (no orientation)
					IConstraint[] c = new IConstraint[4];
					c[0] = new LessOrEqual(new FuncPlus(x[j], w[j]), x[i]); // l1.x>r2.x
					c[1] = new LessOrEqual(new FuncPlus(x[i], w[i]), x[j]); // l2.x>r1.x
					c[2] = new LessOrEqual(new FuncPlus(y[i], h[i]), y[j]); // l1.y<r2.y
					c[3] = new LessOrEqual(new FuncPlus(y[j], h[j]), y[i]); // l2.y<r1.y
					IConstraint[] c1 = new IConstraint[3];
					c1[0] = new IsEqual(o[i], 0);
					c1[1] = new IsEqual(o[j], 0);
					c1[2] = new IsEqual(containerOf[i], containerOf[j]);
					S.post(new Implicate(new AND(c1), new OR(c)));

					// o[i] = o, o[j] = 1
					c = new IConstraint[4];
					c[0] = new LessOrEqual(new FuncPlus(x[j], h[j]), x[i]); // l1.x>r2.x
					c[1] = new LessOrEqual(new FuncPlus(x[i], w[i]), x[j]); // l2.x>r1.x
					c[2] = new LessOrEqual(new FuncPlus(y[i], h[i]), y[j]); // l1.y<r2.y
					c[3] = new LessOrEqual(new FuncPlus(y[j], w[j]), y[i]); // l2.y<r1.y
					IConstraint[] c2 = new IConstraint[3];
					c2[0] = new IsEqual(o[i], 0);
					c2[1] = new IsEqual(o[j], 1);
					c2[2] = new IsEqual(containerOf[i], containerOf[j]);
					S.post(new Implicate(new AND(c2), new OR(c)));

					// o[i] = 1, o[j] = 0
					c = new IConstraint[4];
					c[0] = new LessOrEqual(new FuncPlus(x[j], w[j]), x[i]); // l1.x>r2.x
					c[1] = new LessOrEqual(new FuncPlus(x[i], h[i]), x[j]); // l2.x>r1.x
					c[2] = new LessOrEqual(new FuncPlus(y[i], w[i]), y[j]); // l1.y<r2.y
					c[3] = new LessOrEqual(new FuncPlus(y[j], h[j]), y[i]); // l2.y<r1.y
					IConstraint[] c3 = new IConstraint[3];
					c3[0] = new IsEqual(o[i], 1);
					c3[1] = new IsEqual(o[j], 0);
					c3[2] = new IsEqual(containerOf[i], containerOf[j]);
					S.post(new Implicate(new AND(c3), new OR(c)));

					// o[i] = 1, o[j] = 1
					c = new IConstraint[4];
					c[0] = new LessOrEqual(new FuncPlus(x[j], h[j]), x[i]); // l1.x>r2.x
					c[1] = new LessOrEqual(new FuncPlus(x[i], h[i]), x[j]); // l2.x>r1.x
					c[2] = new LessOrEqual(new FuncPlus(y[i], w[i]), y[j]); // l1.y<r2.y
					c[3] = new LessOrEqual(new FuncPlus(y[j], w[j]), y[i]); // l2.y<r1.y
					IConstraint[] c4 = new IConstraint[3];
					c4[0] = new IsEqual(o[i], 1);
					c4[1] = new IsEqual(o[j], 1);
					c4[2] = new IsEqual(containerOf[i], containerOf[j]);
					S.post(new Implicate(new AND(c4), new OR(c)));
				}
			}
		}
		
		ls.close();
	}
	
	
	
	class BPI{
		int x;
		int y;
		int o;
		int c;
		public BPI(int x, int y, int o, int c){
			this.x = x;
			this.y = y;
			this.o = o;
			this.c = c;
		}
	}
	
	class BP{
		int i;
		int j;
		BPI mi;
		BPI mj;
		public BP(int i, BPI mi, int j, BPI mj){
			this.i = i;
			this.j = j;
			this.mi = mi;
			this.mj = mj;
		}
	}
	
	
	public void restart(){
		for(int i = 0; i < n; i++){
			x[i].setValuePropagate(r.nextInt(maxW + 1));
			y[i].setValuePropagate(r.nextInt(maxH + 1));
			o[i].setValuePropagate(r.nextInt(2));
			containerOf[i].setValuePropagate(r.nextInt(m));
		}
	}
	
	public void updateResult(){
		for(int i = 0; i < n; i++){
			rx[i] = x[i].getValue();
			ry[i] = y[i].getValue();
			ro[i] = o[i].getValue();
			rc[i] = containerOf[i].getValue();
		}
		int v_ = S.violations();
		minViolations = (v_ < minViolations) ? v_ : minViolations;
	}

	/**
	 * Random container cho i và j. Lần lượt ch�?n vị trí i, j đẹp nhất cho 2 item đó.
	 * Tối đa random 100 lần, nếu minDelta vẫn không âm => restart
	 *
	 */
	 
	public void search(int timeLimit) {
		
		
		int l = 0;
		ArrayList list = new ArrayList();
		while ((l <= timeLimit) && (S.violations() > 0)){
				System.out.println(l + " : " + S.violations() + ", best: " + minViolations);
			int minDelta = Integer.MAX_VALUE;
			list.clear();

			int loop = 0;
			int [][][][] mark = new int[n][n][m][m];
			for (int m1 = 0; m1 < n; m1++) {
				for (int m2 = 0; m2 < n; m2++) {
					for (int m3 = 0; m3 < m; m3++) {
						for (int m4 = 0; m4 < m; m4++) {
							mark[m1][m2][m3][m4] = 0;
						}
					}
				}
			}
			int tried = 0;
			int numOfPairs = n * (n - 1) * m * m / 2;
			while (true){
				int i = r.nextInt(n);
				int j = r.nextInt(n);
				// int j = i;
				while (j == i){
					j = r.nextInt(n);
				}
				int ic = r.nextInt(m);
				int jc = r.nextInt(m);
				while (mark[i][j][ic][jc] == 1){
					i = r.nextInt(n);
					j = r.nextInt(n);
					// int j = i;
					while (j == i){
						j = r.nextInt(n);
					}
					ic = r.nextInt(m);
					jc = r.nextInt(m);
				}
				mark[i][j][ic][jc] = 1;
				mark[j][i][jc][ic] = 1;
				tried++;
				int curXi = x[i].getValue();
				int curXj = x[j].getValue();
				int curYi = y[i].getValue();
				int curYj = y[j].getValue();
				int curOi = o[i].getValue();
				int curOj = o[j].getValue();
				int curCi = containerOf[i].getValue();
				int curCj = containerOf[j].getValue();
				int curV = S.violations();
				
				
				x[j].setValuePropagate(curXi);
				y[j].setValuePropagate(curYi);
				// containerOf[j].swapValuePropagate(containerOf[i]); // replace item i and item j
				
				containerOf[i].setValuePropagate(ic);
				containerOf[j].setValuePropagate(jc);
				int curViolations = S.violations();
				ArrayList li = new ArrayList();
				int mDelta = Integer.MAX_VALUE;

				for(int io = 0; io < 2; io++){
					int maxX = W[containerOf[i].getValue()] - (io == 0 ? w[i] : h[i]);
					int maxY = H[containerOf[i].getValue()] - (io == 1 ? w[i] : h[i]);
					for(int ix = 0; ix <= maxX; ix++){
					
						for(int iy = 0; iy <= maxY; iy++){
							
							x[i].setValuePropagate(ix);
							y[i].setValuePropagate(iy);
							o[i].setValuePropagate(io);
							
							int newViolations = S.violations();
							int delta = newViolations - curViolations;
							if (delta < mDelta){
								mDelta = delta;
								li.clear();
								li.add(new BPI(ix, iy, io, ic));
							}
							else if (delta == mDelta){
								li.add(new BPI(ix, iy, io, ic));
							}
							
						}
					}
					
				}
				
				
				BPI mi = (BPI) li.get(r.nextInt(li.size()));
				x[i].setValuePropagate(mi.x);
				y[i].setValuePropagate(mi.y);
				o[i].setValuePropagate(mi.o);
				mDelta = Integer.MAX_VALUE;
				
				curViolations = S.violations();
				li.clear();

				for(int jo = 0; jo < 2; jo++){
					int maxX = W[containerOf[j].getValue()] - (jo == 0 ? w[j] : h[j]);
					int maxY = H[containerOf[j].getValue()] - (jo == 1 ? w[j] : h[j]);
					for(int jx = 0; jx <= maxX; jx++){
					
						for(int jy = 0; jy <= maxY; jy++){
							
							x[j].setValuePropagate(jx);
							y[j].setValuePropagate(jy);
							o[j].setValuePropagate(jo);
							
							int newViolations = S.violations();
							int delta = newViolations - curViolations;
							if (delta < mDelta){
								mDelta = delta;
								li.clear();
								li.add(new BPI(jx, jy, jo, jc));
							}
							else if (delta == mDelta){
								li.add(new BPI(jx, jy, jo, jc));
							}
							
						}
					}
							
				}
				
				
				BPI mj = (BPI) li.get(r.nextInt(li.size()));
				x[j].setValuePropagate(mj.x);
				y[j].setValuePropagate(mj.y);
				o[j].setValuePropagate(mj.o);
				int newViolations = S.violations();
				int delta = newViolations - curV;
				if (delta < minDelta){
					minDelta = delta;
					list.clear();
					list.add(new BP(i, mi, j, mj));
				}
				else if (delta == minDelta){
					list.add(new BP(i, mi, j, mj));
				}
				x[i].setValuePropagate(curXi);
				x[j].setValuePropagate(curXj);
				y[i].setValuePropagate(curYi);
				y[j].setValuePropagate(curYj);
				o[i].setValuePropagate(curOi);
				o[j].setValuePropagate(curOj);
				// containerOf[i].swapValuePropagate(containerOf[j]);
				containerOf[i].setValuePropagate(curCi);
				containerOf[j].setValuePropagate(curCj);
				loop++;
				if (minDelta < 0){
					break;
				}
				if (tried >= numOfPairs){
					break;
				}
				// System.out.println("tried: " + tried);
				
			}
			if (minDelta < 0){
				BP move = (BP) list.get(r.nextInt(list.size()));
				x[move.i].setValuePropagate(move.mi.x);
				y[move.i].setValuePropagate(move.mi.y);
				o[move.i].setValuePropagate(move.mi.o);
				x[move.j].setValuePropagate(move.mj.x);
				y[move.j].setValuePropagate(move.mj.y);
				o[move.j].setValuePropagate(move.mj.o);
				// containerOf[move.i].swapValuePropagate(containerOf[move.j]);
				containerOf[move.i].setValuePropagate(move.mi.c);
				containerOf[move.j].setValuePropagate(move.mj.c);
				updateResult();
			}
			else {
				System.out.println("restart");
				restart();
			}
			l++;
		}
		
	}
	 // End

	public void print() {
		for (int c = 0; c < m; c++) {

			for (int i = 0; i < n; i++) {
				int c_ = containerOf[i].getValue();
				if (c_ == c){
					System.out.println("item " + (i + 1) + " :  " + c + " " + x[i].getValue()
						+ " " + y[i].getValue() + " ->  " + (w[i]) + " " + (h[i])
						+ " " + o[i].getValue());
				}
			}
		}
	}
	
	
	public void printResultHTML(String fn){
		int[] rx = new int[x.length];
		int[] ry = new int[y.length];
		int[] ro = new int[o.length];
		int[] rc = new int[x.length];
		for(int i = 0; i < x.length; i++){
			rx[i] = x[i].getValue();
			ry[i] = y[i].getValue();
			ro[i] = o[i].getValue();
			rc[i] = containerOf[i].getValue();
		}
		for(int i = 0; i < rx.length; i++){
			System.out.print(rx[i] + ",");
		}
		System.out.println();
		for(int i = 0; i < ry.length; i++){
			System.out.print(ry[i] + ",");
		}
		System.out.println();
		for(int i = 0; i < ro.length; i++){
			System.out.print(ro[i] + ",");
		}
		System.out.println();
		
		outTableNew(fn,n,w,h,rx,ry,ro, rc);
	}
	
	
	public void outTableNew(String fn, int n, int[] w, int[] h, int[] x, int[] y, int[] o, int[] c) {
	        final String[] Color = new String[]{
	                "#FFFF00", "#1CE6FF", "#FF34FF", "#FF4A46", "#008941", "#006FA6", "#A30059",
	                "#FF0000", "#7A4900", "#0000A6", "#63FFAC", "#B79762", "#004D43", "#8FB0FF", "#997D87",
	                "#5A0007", "#809693", "#1B4400", "#4FC601", "#3B5DFF", "#4A3B53", "#FF2F80",
	                "#61615A", "#BA0900", "#6B7900", "#00C2A0", "#FFAA92", "#FF90C9", "#B903AA", "#D16100",
	                "#FFDBE5", "#000035", "#7B4F4B", "#A1C299", "#300018", "#0AA6D8", "#013349", "#00846F",
	                "#372101", "#FFB500", "#C2FFED", "#A079BF", "#CC0744", "#C0B9B2", "#C2FF99", "#001E09",
	                "#00489C", "#6F0062", "#0CBD66", "#EEC3FF", "#456D75", "#B77B68", "#7A87A1", "#788D66",
	                "#885578", "#FAD09F", "#FF8A9A", "#D157A0", "#BEC459", "#456648", "#0086ED", "#886F4C",
	                "#34362D", "#B4A8BD", "#00A6AA", "#452C2C", "#636375", "#A3C8C9", "#FF913F", "#938A81",
	                "#575329", "#00FECF", "#B05B6F", "#8CD0FF", "#3B9700", "#04F757", "#C8A1A1", "#1E6E00",
	                "#7900D7", "#A77500", "#6367A9", "#A05837", "#6B002C", "#772600", "#D790FF", "#9B9700",
	                "#549E79", "#FFF69F", "#201625", "#72418F", "#BC23FF", "#99ADC0", "#3A2465", "#922329",
	                "#5B4534", "#FDE8DC", "#404E55", "#0089A3", "#CB7E98", "#A4E804", "#324E72", "#6A3A4C",
	                "#83AB58", "#001C1E", "#D1F7CE", "#004B28", "#C8D0F6", "#A3A489", "#806C66", "#222800",
	                "#BF5650", "#E83000", "#66796D", "#DA007C", "#FF1A59", "#8ADBB4", "#1E0200", "#5B4E51",
	                "#C895C5", "#320033", "#FF6832", "#66E1D3", "#CFCDAC", "#D0AC94", "#7ED379", "#012C58"
	        };
	        try {
	            File outFile = new File(fn);
	            PrintWriter out;
	            out = new PrintWriter(outFile);
	            out.println("<!doctype html>\n<html>\n<head>\n<title>Binpacking2D</title>\n</head>\n<body>\n");

	            boolean[] isIndex  = new boolean[n+2];
	            
	            
	            
	            int size = 650 / (Math.max(maxW, maxH) + 1);
	            out.println("<style type=\"text/css\">\n" + "table, td {\n" +
	                            "\t\tborder : 1px solid black;\n" +
	                            "\t\tborder-collapse: collapse;text-align : center;\n" +
	                            "\t}\n" +
	                            "\ttd {\n" +
	                            "\t\twidth : +" + size + "px;\n" +
	                            "\t\theight: +" + size + "px;\n" +
	                            "\t}"
	            );
	            for (int i = 0; i < n; i++) {
	                out.println("td.class" + (i) + " { \n background-color:" + Color[i] + ";  \n}");
	            }
	            out.println("</style>");

	            for(int ic = 0; ic < m; ic++){
	            	out.println("<br />");
	            	out.println("<br />");
	            	out.println("<table>");
	            	int H_ = H[ic];
	            	int W_ = W[ic];
		            for (int i = 0; i <= H_; i++) {
		                out.println("<tr>");
		                for (int j = 0; j <= W_; j++) {
		                    if (i == 0) {
		                        if (j == 0) {
		                            out.print("<td>");
		                            out.println("</td>");
		                        } else {
		                            out.print("<td>");
		                            out.print(j);
		                            out.println("</td>");
		                        }
		                    } else {
		                        if (j == 0) {
		                            out.print("<td>");
		                            out.print(i);
		                            out.println("</td>");
		                        } else {
		                            boolean flag = false;
		                            for (int k = 0; k < n; k++) {
		                                if (ic == c[k]){
		                                	int xk = x[k];//x[k].getValue();
			                                int yk = y[k];//y[k].getValue();
			                                int wk = w[k];
			                                int hk = h[k];
			                                //if (o[k].getValue() == 0) {
			                                if (o[k] == 0) {
			                                    if (j - 1 >= xk && j - 1 <= xk + wk - 1 && i - 1 >= yk && i - 1 <= yk + hk - 1) {
			                                        out.print("<td class='class" + k + "'>");

			                                        if(!isIndex[k] && (j-1)==(xk+xk+wk-1)/2 && (i-1)==(yk+yk+hk-1)/2){
			                                            out.print(k);
			                                            isIndex[k]=true;
			                                        }
			                                        flag = true;
			                                        break;
			                                    }
			                                } else {
			                                    if (j - 1 >= xk && j - 1 <= xk + hk - 1 && i - 1 >= yk && i - 1 <= yk + wk - 1) {
			                                        out.print("<td class='class" + k + "'>");
			                                        if(!isIndex[k] && (j-1)==(xk+xk+hk-1)/2 && (i-1)==(yk+yk+wk-1)/2){
			                                            out.print(k);
			                                            isIndex[k]=true;
			                                        }
			                                        flag = true;
			                                        break;
			                                    }
			                                }
		                                }
		                            }
		                            if (flag) out.println("</td>");
		                            else {
		                                out.print("<td>");
		                                out.println("</td>");
		                            }
		                        }
		                    }

		                }
		                out.println("</tr>");
		            }
		            out.println("</table>");
	            }

	            out.println("</body></html>");
	            out.close();
	        } catch (IOException exx) {
	            exx.printStackTrace();
	        }
	}
	
	
	public boolean solve(int timeLimit) {
		stateModel();
		search(timeLimit);
		print();
		// outCanvas();
		//outTable("binpacking2D.html");
		return S.violations() == 0;
	}

	public void testBatch(String filename, int nbTrials, int timeLimit) {
		BinPacking2DMCCSNew2 bp = new BinPacking2DMCCSNew2();
		bp.readData(filename);
		double[] t = new double[nbTrials];
		double avg_t = 0;
		int nbSolved = 0;
		for (int k = 0; k < nbTrials; k++) {
			double t0 = System.currentTimeMillis();
			boolean ok = bp.solve(timeLimit);
			
			t[k] = (System.currentTimeMillis() - t0) * 0.001;
			if (ok) {
				nbSolved++;
				avg_t += t[k];
			}
		}
		avg_t = avg_t * 1.0 / nbSolved;
		System.out.println("Time = " + avg_t + ", nbSolved = " + nbSolved);
	}

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		
		 BinPacking2DMCCSNew2 bp = new BinPacking2DMCCSNew2();
		 //bp.readData("data\\BinPacking2D\\bin-packing-2D-W19-H20-I21.txt");
//		 bp.readData("data\\BinPacking2D\\bin-packing-2D-W19-H19-I21.txt");
		 bp.readData("BinPacking2DMC-m3-n27.txt");
		 bp.solve(1000);
//		 bp.outCanvas();
		 // bp.outTable("OpenCBLS-binpacking2D.html");
		 bp.printResultHTML("Binpacking2DMC.html");
		/*
		BinPacking2D bp = new BinPacking2D();
		bp.testBatch("data\\BinPacking2D\\bin-packing-2D-W19-H19-I21.txt", 10,300);
		 */
	}

}