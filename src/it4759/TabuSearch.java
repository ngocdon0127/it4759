package it4759;

import java.util.ArrayList;
import java.util.Random;

import localsearch.model.IConstraint;
import localsearch.model.VarIntLS;

public class TabuSearch {

	VarIntLS[] x;
	IConstraint cs;
	int maxIter;
	int minViolations;
	Random r;
	int[] result;
	int tabu[][];
	int tabuLen;
	
	
	
	
	public TabuSearch(IConstraint cs, int maxIter, int tabuLen){
		this.cs = cs;
		this.maxIter = maxIter;
		this.tabuLen = tabuLen;
		minViolations = Integer.MAX_VALUE;
		r = new Random();
		x = cs.getVariables();
		result = new int[x.length];
		
		// initialize tabu table
		int max = -1;
		for(int i = 0; i < x.length; i++){
			int max_ = x[i].getMaxValue();
			max = (max < max_) ? max_ : max;
		}
		tabu = new int[x.length][max + 1];
		for(int i = 0; i < x.length; i++){
			for(int j = 0; j <= max; j++){
				tabu[i][j] = 0;
			}
		}
	}
	
	public void restart(){
		for(int i = 0; i < x.length; i++){
			x[i].setValuePropagate(r.nextInt(x[i].getMaxValue() - x[i].getMinValue() + 1) + x[i].getMinValue());
		}
	}
	
	public void updateResult(){
		minViolations = cs.violations();
		for(int i = 0; i < x.length; i++){
			result[i] = x[i].getValue();
		}
	}
	
	class TabuMove{
		int i;
		int v;
		public TabuMove(int i, int v){
			this.i = i;
			this.v = v;
		}
	}
	
	public void search(){
		int l = 0;
		ArrayList list = new ArrayList();
		while ((l <= maxIter) && (cs.violations() > 0)){
			if (l % 1000 == 0){
				System.out.println(l + " : " + cs.violations());
			}
			int minDelta = Integer.MAX_VALUE;
//			ArrayList list = new ArrayList();
			list.clear();
			for(int i = 0; i < x.length; i++){
				int min = x[i].getMinValue();
				int max = x[i].getMaxValue();
				int cur = x[i].getValue();
				for(int v = min; v <= max; v++){
					if ((cur != v) && (tabu[i][v] <= l)){
						int delta = cs.getAssignDelta(x[i], v);
						if (delta < minDelta){
							minDelta = delta;
							list.clear();
							list.add(new TabuMove(i, v));
						}
						else if (delta == minDelta){
							list.add(new TabuMove(i, v));
						}
					}
				}
				
				
			}
			if (minDelta < 0){
				TabuMove move = (TabuMove) list.get(r.nextInt(list.size()));
				x[move.i].setValuePropagate(move.v);
				tabu[move.i][move.v] += tabuLen;
				updateResult();
			}
			else {
				restart();
			}
			l++;
		}
		System.out.println("best: " + minViolations);
		for(int i = 0; i < result.length; i++){
			x[i].setValuePropagate(result[i]);
		}
	}
	
}
