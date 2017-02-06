package it4759;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Random;

public class NQueens {
	
	private int x[];
	private int n;
	Random r;
	
	public NQueens(int n){
		this.n = n;
		x = new int[n];
		r = new Random();
	}
	
	private int conflict(){
		int c = 0;
		for(int i = 0; i < this.n; i++){
			c += this.conflict(i);
		}
		return c / 2;
	}
	
	private int conflict(int index){
		int c = 0;
		for(int i = 0; i < this.n; i++){
			if (i != index){
				if (x[index] == x[i]){
					c++;
				}
				
				if (x[index] - index == x[i] - i){
					c++;
				}
				
				if (x[index] + index == x[i] + i){
					c++;
				}
			}
		}
		return c;
	}
	
	private void init(){
		for(int i = 0; i < n; i++){
			x[i] = r.nextInt(this.n);
		}
	}
	
	private int move(int index){
		int min = Integer.MAX_VALUE;
		int oldValue = x[index];
		ArrayList list = new ArrayList();
		for(int i = 0; i < this.n; i++){
			x[index] = i;
			int conflicts = this.conflict(index);
			if (conflicts < min){
				min = conflicts;
				list.clear();
				list.add(i);
			}
			else if (conflicts == min){
				list.add(i);
			}
		}
		
		x[index] = (int) list.get(this.r.nextInt(list.size()));
		return x[index];
		
	}
	
	private void solve(){
		int l = 0;
		this.init();
		while (l < 10000){
			int totalConflicts = this.conflict();
			System.out.println(l + " : " + totalConflicts);
			if (totalConflicts == 0){
				break;
			}
			ArrayList list = new ArrayList();
			int max = -1;
			for(int i = 0; i < this.n; i++){
				int c = this.conflict(i);
				if (c > max){
					max = c;
					list.clear();
					list.add(i);
				}
				else if (c == max){
					list.add(i);
				}
			}
			
			this.move((int) list.get(this.r.nextInt(list.size())));
			l++;
			
		}
	}

	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		NQueens nQueens = new NQueens(100);
		nQueens.solve();
		File f = new File("NQueens.html");
		FileOutputStream fos = new FileOutputStream(f);
		OutputStreamWriter osw = new OutputStreamWriter(fos);
		BufferedWriter bw = new BufferedWriter(osw);
		bw.write("<style>table, tr, td{border: 1px solid black;} tr, td{height: 20px} td{width: 20px}</style>\n");
		bw.write("<table style='border-collapse: collapse'>\n");
		for(int i = 0; i < nQueens.n; i++){
			bw.write("<tr>\n");
			for(int j = 0; j < nQueens.n; j++){
				if (nQueens.x[i] == j){
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
