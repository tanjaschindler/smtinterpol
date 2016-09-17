package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

public class DawgFactory<LETTER, COLNAMES> {
	
	EprTheory mEprTheory;
	Set<LETTER> mAllConstants;
	
	public DawgFactory(Set<LETTER> allConstants, EprTheory eprTheory) {
		mEprTheory = eprTheory;
		mAllConstants = allConstants;
	}

	public IDawg<LETTER, COLNAMES> createEmptyDawg(SortedSet<COLNAMES> termVariables) {
		assert termVariables != null;
		//TODO freeze the current allConstants set, here?? or can it just change transparently?? 
		return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllConstants);
	}

	/**
	 * Creates and returns a Dawg that accepts all words in Sigma^n.
	 * (where n = termVariables.length)
	 *
	 * @param termVariables
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> createFullDawg(SortedSet<COLNAMES> termVariables) {
		assert termVariables != null;
		return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllConstants).complement();
	}

	public IDawg<LETTER, COLNAMES> copyDawg(IDawg<LETTER, COLNAMES> dawg) {
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) dawg;
		return new NaiveDawg<LETTER, COLNAMES>(nd);
	}
	
	
	/**
	 * Returns a dawg that is the same as the input dawg, but the columns have been renamed according 
	 * to the given map.
	 * Note that the map may introduce repetitions in the column names.
	 *   For example the signature of dawg might be (u, v, w), and the map might be [u -> x, v -> x, w -> y].
	 *   The consequence is that the signature of the new dawg will be (x, y). We will only take points
	 *   from the input dawg that have the same entry for u and v.
	 *     (select + project)
	 *     
	 * 
	 * @param dawg a dawg whose column names are to be changed
	 * @param translation map that gives every column a new name
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> renameColumnsOfDawg(
			IDawg<LETTER, COLNAMES> dawg, Map<COLNAMES, COLNAMES> translation) {
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) dawg;
		return new NaiveDawg<LETTER, COLNAMES>(nd, translation);
	}

	public IDawg<LETTER, COLNAMES> createJoinDawg(Map<ClauseLiteral, DecideStackLiteral> mHistory,
			ClauseLiteral mWatchedLiteral) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Create a dawg from the input dawg where only the points are selected that match the given mapping.
	 * The mappings says for some columns what value they must have.
	 * (this is a special version of the normal select operation sigma_phi, where phi has the form x=a, 
	 *  for a column name x and a letter a)
	 * 
	 * @param dawg
	 * @param selectMap (possibly) restricts some COLNAMES in the signature to only one LETTER
	 * @return
	 */
	public IDawg<ApplicationTerm, TermVariable> select(IDawg<ApplicationTerm, TermVariable> dawg,
			Map<TermVariable, ApplicationTerm> selectMap) {
		return dawg.select(selectMap);
	}

	public IDawg<LETTER, COLNAMES> renameSelectAndProject(
			IDawg<LETTER, COLNAMES> other, Map<COLNAMES, Object> translation, SortedSet<COLNAMES> targetSignature) {

		COLNAMES colNamesInstance = other.getColnames().first();
		
		// the signature of the new dawg has only the non-duplicated colnames 
		// and also omits constants (i.e. objects not of the type COLNAMES)
		// this signature is before the blowup to targetSignature
		SortedSet<COLNAMES> newPointSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		for (Object o : translation.values()) {
			if (colNamesInstance.getClass().isInstance(o)) {
				newPointSignature.add((COLNAMES) o);
			}
		}
		
		Map<COLNAMES, Integer> newSigColNamesToIndex = EprHelpers.computeColnamesToIndex(newPointSignature);
		
		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) other;
//		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>();
		NaiveDawg<LETTER, COLNAMES> result = new NaiveDawg<LETTER, COLNAMES>(targetSignature, mAllConstants);

		for (List<LETTER> point : otherNd.mBacking) {

			List<LETTER> newPoint = new ArrayList<LETTER>(newPointSignature.size());
			// set up the new point (need to fill it, or List.set(..) won't work)
			for (int i = 0; i < newPointSignature.size(); i++) {
				newPoint.add(null);
			}
			
			// tracks if a column name has been seen, and what letter it had been assigned (does select_x=x so to say)
			Map<COLNAMES, LETTER> variableAssignmentInPoint = new HashMap<COLNAMES, LETTER>();
			
			Iterator<COLNAMES> ptColIt = other.getColnames().iterator();
			for (int i = 0; i < point.size(); i++) {
				LETTER ptLtr = point.get(i);
				COLNAMES ptColnameInOldSig = ptColIt.next();

				Object trans = translation.get(ptColnameInOldSig);
				if (colNamesInstance.getClass().isInstance(trans)) {
					COLNAMES ptColnameInNewSig = (COLNAMES) trans;
					
					LETTER vaip = variableAssignmentInPoint.get(ptColnameInNewSig);
					if (vaip != null && vaip != ptLtr) {
						// violation of select_x=x
						newPoint = null;
						break;
					} else {
						newPoint.set(newSigColNamesToIndex.get(ptColnameInNewSig), ptLtr);
						// store that at the current oldColumn-name we used letter ptLtr
						variableAssignmentInPoint.put(ptColnameInNewSig, ptLtr);
					}
					
				} else {
					// we have a constant in the column where this letter in the point is supposed to "land"
					// select_x=c so to say..
					if (ptLtr.equals(trans)) {
						// the constant matches go on (add nothing to the new point)
					} else {
						// point is filtered by the select that checks the constants
						newPoint = null;
						break;
					}
				}

			}
			if (newPoint != null) {
				result.addWithSubsetSignature(newPoint, newPointSignature);
//				newBacking.add(newPoint);
			}
		}

		return result;
	}

	/**
	 * From the input dawg and translation computes a dawg
	 *  - whose signature is the range of the translation mapping
	 *  - the input dawg's signature is shorter or of equal length of the new signature
	 *  - whose points are rearranged according to the new signature
	 *  - constants in the argList are filled in the corresponding places at every point
	 *  - we exploit that the order of arglist matches the sorting order of the newSignature 
	 *    (that is fix for the given eprPredicate)
	 * @param other
	 * @param translation a map translating the colnames of the old dawg ("other") to the colnames of the new dawg
	 *                    may not have a preimage for every new colname in the new signature because there constants 
	 *                    from argList are filled in
	 *                     (could be computed from arglist, right?..)
	 * @param argList
	 * @param newSignature
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> renameColumnsAndRestoreConstants(
			IDawg<LETTER, COLNAMES> other, 
			Map<COLNAMES, COLNAMES> translation, 
			List<Object> argList, 
			SortedSet<COLNAMES> newSignature) {
		
		assert argList.size() == newSignature.size();

		Map<COLNAMES, Integer> newSigColnamesToIndex = EprHelpers.computeColnamesToIndex(newSignature);
		Map<COLNAMES, Integer> oldSigColnamesToIndex = EprHelpers.computeColnamesToIndex(other.getColnames());

		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>();
		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) other;
		
		for (List<LETTER> point : otherNd.mBacking) {
			List<LETTER> newPoint = new ArrayList<LETTER>(newSignature.size());
			// add placeholders so we can later use List.set(..)
			for (int i = 0; i < newSignature.size(); i++) {
				newPoint.add(null);
			}

			Iterator<COLNAMES> newSigColIt = newSignature.iterator();
			for (int i = 0; i < argList.size(); i++) {
				// argList provides us with the colname of the old signature or a constant for each position
				COLNAMES newSigColname = translation.get(argList.get(i));
				if (newSigColname == null) {
					// argList.get(i) must be a constant, as translation translates all termVariables
					assert newPoint.get(i) == null :
						"the translation map must not translate to a colname where the clauseliteral has a constant!";
					newPoint.set(i, (LETTER) argList.get(i));
				} else {
					Integer oldSigIndex = oldSigColnamesToIndex.get(argList.get(i));
					assert newPoint.get(newSigColnamesToIndex.get(newSigColname)) == null :
						"the translation map must not translate to a colname where the clauseliteral has a constant!";
					newPoint.set(newSigColnamesToIndex.get(newSigColname), point.get(oldSigIndex));
				}
			}
			newBacking.add(newPoint);
		}
		
		return new NaiveDawg<LETTER, COLNAMES>(newSignature, mAllConstants, newBacking);
	}

	/////////////////////////////////////////////////////////////
	///////////////// test code /////////////////////////////////
	/////////////////////////////////////////////////////////////
		/**
		 *  Some tests for the DawgFactory
		 * @param args
		 */
		public static void main(String[] args) {
			
			// setup 
			
			Set<Character> constants = new HashSet<Character>();
			constants.add('a');
			constants.add('b');
			constants.add('c');
			
			
			DawgFactory<Character, String> df = 
					new DawgFactory<Character, String>(constants, null);
			
			SortedSet<String> colNames1 = new TreeSet<String>();
			colNames1.add("one");
			colNames1.add("two");
	//		colNames1.add("three");
	//		colNames1.add("four");
	//		colNames1.add("five");
			
			SortedSet<String> colNames2 = new TreeSet<String>();
			colNames2.add("alpha");
			colNames2.add("beta");
			colNames2.add("gamma");
	//		colNames1.add("delta");
	
	
			IDawg<Character, String> d1 = df.createFullDawg(colNames1);
	
			System.out.println("d1: (one, two), Sigma^*");
			System.out.println(d1);
	
			IDawg<Character, String> d2 = df.createEmptyDawg(colNames2);
			List<Character> word1 = new ArrayList<Character>();
			word1.add('a');
			word1.add('a');
			word1.add('b');
			d2.add(word1);
			
			List<Character> word2 = new ArrayList<Character>();
			word2.add('a');
			word2.add('b');
			word2.add('b');
			d2.add(word2);
	
			System.out.println("d2: (alpha, beta, gamma), { aab, abb } ");
			System.out.println(d2);
			
			// tests for renameSelectAndProject
			
			Map<String, Object> translation3 = new HashMap<String, Object>();
			translation3.put("alpha", "bla");
			translation3.put("beta", "bla");
			translation3.put("gamma", "blub");
	
			IDawg<Character, String> d3 = df.renameSelectAndProject(d2, translation3, d2.getColnames());
	
			System.out.println("d3: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> blub)");
			System.out.println("expecting: (bla, blub) {ab}");
			System.out.println(d3);
			
			Map<String, Object> translation4 = new HashMap<String, Object>();
			translation4.put("alpha", "bla");
			translation4.put("beta", "bla");
			translation4.put("gamma", 'a');
	
			IDawg<Character, String> d4 = df.renameSelectAndProject(d2, translation4, d2.getColnames());
	
			System.out.println("d4: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> 'a')");
			System.out.println("expecting: (bla) {}");
			System.out.println(d4);
	
			Map<String, Object> translation5 = new HashMap<String, Object>();
			translation5.put("alpha", "bla");
			translation5.put("beta", "bla");
			translation5.put("gamma", 'b');
	
			IDawg<Character, String> d5 = df.renameSelectAndProject(d2, translation5, d2.getColnames());
	
			System.out.println("d5: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> 'b')");
			System.out.println("expecting: (bla) {a}");
			System.out.println(d5);
	
			// tests for renameAndRestoreConstants
			
			Map<String, String> translation6 = new HashMap<String, String>();
			translation6.put("alpha", "cinque");
			translation6.put("beta", "uno");
			translation6.put("gamma", "quattro");
			
			List<Object> argList1 = new ArrayList<Object>();
			argList1.add("beta");
			argList1.add('B');
			argList1.add("gamma");
			argList1.add('A');
			argList1.add("alpha");
			
			SortedSet<String> newSignature1 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
			newSignature1.add("uno");
			newSignature1.add("due");
			newSignature1.add("tre");
			newSignature1.add("quattro");
			newSignature1.add("cinque");

			
			IDawg<Character, String> d6 = df.renameColumnsAndRestoreConstants(d2, translation6, argList1, newSignature1);

			System.out.println("d6: rnRc(d2, {alpha -> uno, beta -> due, gamma -> tre), "
					+ "(beta, B, gamma, A, alpha)" +  newSignature1);
			System.out.println("expecting: (due, cinque, quattro, tre, uno) {aBbAa, aBbAb}");
			System.out.println(d6);
		
		}

		public IDawg<LETTER, COLNAMES> createOnePointDawg(
				SortedSet<COLNAMES> sig, List<LETTER> point) {
			NaiveDawg<LETTER, COLNAMES> dawg = 
					new NaiveDawg<LETTER, COLNAMES>(sig, mAllConstants);
			dawg.add(point);
			return dawg;
		}

		public IDawg<LETTER, COLNAMES> addAllWithSubsetSignature(
				IDawg<LETTER, COLNAMES> baseDawg,
				IDawg<LETTER, COLNAMES> toBeAdded) {
			NaiveDawg<LETTER, COLNAMES> nd = new NaiveDawg<LETTER, COLNAMES>(
					baseDawg.getColnames(), 
					mAllConstants, 
					((NaiveDawg<LETTER, COLNAMES>) baseDawg).mBacking);
			nd.addAllWithSubsetSignature(toBeAdded);
			return nd;
		}
	
}