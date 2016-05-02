package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;

public class EprNonUnitClause extends EprClause {

	private EprUnitClause mUnitLiteral;
	private EprNonUnitClause mInstantiationOfClauseForCurrentUnitLiteral;

	private int mNoFulfillableLiterals;

	HashSet<Literal> mFulfilledLiterals = new HashSet<Literal>();
	
	private HashMap<Literal, FulfillabilityStatus> mFulfillabilityStatus = new HashMap<Literal, FulfillabilityStatus>();

	private HashMap<Literal, HashSet<EprUnitClause>> mLiteralToUnfulfillabilityReasons = new HashMap<>();

	
	
	public EprNonUnitClause(Literal[] literals, Theory theory, EprStateManager stateManager) {
		super(literals, theory, stateManager);
		// TODO Auto-generated constructor stub
		setUp();
	}
	
	private void setUp() {
		// is this a unit clause upon creation?
		if (groundLiterals.length == 0
				&& eprQuantifiedPredicateLiterals.length == 1) {
			Literal lit = eprQuantifiedPredicateLiterals[0];
			EprQuantifiedLitWExcptns eqlwe = EprHelpers.buildEQLWE(
					lit.getSign() == 1, 
					(EprQuantifiedPredicateAtom) lit.getAtom(), 
					eprEqualityAtoms, this,
					mTheory, mStateManager);
			mUnitLiteral = eqlwe;
		} else if (groundLiterals.length == 1
				&& eprQuantifiedPredicateLiterals.length == 0) {
			if (eprEqualityAtoms.length == 0) {
				mUnitLiteral = new EprGroundUnitClause(groundLiterals[0], 
						mTheory, mStateManager, "is this used? (EprClause.SetupClauses)");
			} else {
				assert false : "quantified equalities but not quantified literals: "
						+ "this should have been caught before";
			}
		}
		
		// set fulfillability status
		mNoFulfillableLiterals = 0;

		setLiteralStates();
		
		if (mNoFulfillableLiterals == 1)
			searchUnitLiteral();

	}
	
	/**
	 * @return the only literal in the clause that is still fulfillable, null, if there is no such literal
	 */
//	public UnFulReason getUnitClauseLiteral() {
	public EprUnitClause getUnitClauseLiteral() {
		if (!mFulfilledLiterals.isEmpty()) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null;
		}
		if (this.mUnitLiteral == null) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null;
		}
//		if (this.mUnitLiteral.mLiteral != null &&
//				!(this.mUnitLiteral.mLiteral.getAtom() instanceof EprQuantifiedPredicateAtom)) {
		if (this.mUnitLiteral instanceof EprGroundUnitClause) {	// unit literal is ground
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return mUnitLiteral;
		}
		
		//if the unitLiteral is a quantified literal, then we first have to find out if there is 
		// a unifier with the conflicts because of which we set the others "unfulfillable"
		// if not, we cannot do a unitpropagation
		ArrayDeque<HashSet<TermTuple>> conflictPointSets = new ArrayDeque<>();
		ArrayDeque<TermTuple> pointsFromLiterals = new ArrayDeque<>();
		EprQuantifiedLitWExcptns quantUnitLit = (EprQuantifiedLitWExcptns) mUnitLiteral;

		for (Literal li : eprQuantifiedPredicateLiterals) {
			if (li.equals(quantUnitLit.getPredicateLiteral()))
				continue;
			EprQuantifiedPredicateAtom liAtom = (EprQuantifiedPredicateAtom) li.getAtom();
			pointsFromLiterals.add(liAtom.getArgumentsAsTermTuple());
			conflictPointSets.add(new HashSet<TermTuple>());
			HashSet<EprUnitClause> ur = mLiteralToUnfulfillabilityReasons.get(li);
			for (EprUnitClause ufr : ur) {
//				if (ufr.mLiteral != null) {
				if (ufr instanceof EprGroundUnitClause) {
//					conflictPointSets.getLast().add(((EprGroundPredicateAtom) ufr.mLiteral.getAtom()).getArgumentsAsTermTuple());
					EprGroundPredicateAtom ua  = (EprGroundPredicateAtom) ((EprGroundUnitClause) ufr).getLiteral().getAtom();
					conflictPointSets.getLast().add(ua.getArgumentsAsTermTuple());
				} else {
					EprQuantifiedLitWExcptns eqlwe = (EprQuantifiedLitWExcptns) ufr;
					if (eqlwe.mExceptions.length == 0) {
						conflictPointSets.getLast().add(eqlwe.getPredicateAtom().getArgumentsAsTermTuple());
					} else {
						//TODO : probably we need to track, and later use the equalities 
						// that are created when resolving the literal with its UnFulReason
						assert false : "not yet implemented -- what to do with excepted points??";
					}
				}
			}
		}
		
		TTSubstitution sub = new ComputeInstantiations(conflictPointSets, pointsFromLiterals)
				.getSubstitution();

		if (sub == null) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null; // if there is no unifier, then this clause actually is no unit clause
		}
		EprUnitClause unifiedUnitLiteral = null;
		if (sub.isEmpty()) {  //TODO is emptiness enough to check?
//			unification is trivial, no need for a derived clause
			unifiedUnitLiteral = mUnitLiteral;
		} else {
//			if (mUnitLiteral.mLiteral != null) {
			if (mUnitLiteral instanceof EprGroundUnitClause) {
//				unifiedUnitLiteral = new UnFulReason(EprHelpers
//						.applySubstitution(sub, mUnitLiteral.mLiteral, mTheory)); 
				Literal substLit = EprHelpers.applySubstitution(sub, 
								((EprGroundUnitClause) mUnitLiteral).getLiteral(), mTheory);
						
						
				unifiedUnitLiteral = new EprGroundUnitClause(substLit, mTheory, mStateManager, null);
				 //TODO: register the new literal somewhere???
				
//				if (mStateManager.isSubsumedInCurrentState(unifiedUnitLiteral.mLiteral)) { // already set??
				if (mStateManager.isSubsumedInCurrentState(unifiedUnitLiteral)) { // already set??
					mUnitLiteral = null;
					return null; //TODO: seems incomplete, maybe we want to propagate other points, then..
				}
			} else {
				EprQuantifiedLitWExcptns rawUnitEqlwe = (EprQuantifiedLitWExcptns) mUnitLiteral;
				

				Literal realLiteral = EprHelpers.applySubstitution(sub, 
						rawUnitEqlwe.getPredicateLiteral(), mTheory);
				EprPredicateAtom realAtom = (EprPredicateAtom) realLiteral.getAtom();

//				ArrayList<Literal> exceptions = new ArrayList<>();
//						Arrays.asList(eprEqualityAtoms)); 
				ArrayList<EprEqualityAtom> exceptions = new ArrayList<>();
				ArrayList<DPLLAtom> eqs = rawUnitEqlwe.substituteInExceptions(sub, mTheory);
				for (DPLLAtom eq : eqs) {
					if (eq instanceof EprEqualityAtom) {
						exceptions.add((EprEqualityAtom) eq);
					} else if (eq instanceof CCEquality) {
						assert false : "TODO: do";
					} else 
						assert false : "should not happen";
				}
				

				if (realAtom instanceof EprQuantifiedPredicateAtom) {
					EprQuantifiedLitWExcptns realUnitEqlwe = EprHelpers.buildEQLWE(
							realLiteral.getSign() == 1, 
							(EprQuantifiedPredicateAtom) realAtom, 
							exceptions.toArray(new EprEqualityAtom[exceptions.size()]), 
							this, mTheory, mStateManager);
					unifiedUnitLiteral = realUnitEqlwe;
				} else {
					unifiedUnitLiteral = new EprGroundUnitClause(realLiteral, 
							mTheory, mStateManager, null);
				}
				
			}
			mInstantiationOfClauseForCurrentUnitLiteral = (EprNonUnitClause) this.instantiateClause(null, sub);
			mStateManager.addDerivedClause(mInstantiationOfClauseForCurrentUnitLiteral);
		}
		return unifiedUnitLiteral;
	}
	
	/**
	 * If this is a unit clause, then this yield the explanation clause, which is this clause instantiated in a way
	 *  such that it really is a unit clause 
	 *  (i.e. a ground unit clause or a set of such -- for a partial instantiation of the freevars..)
	 *  TODO: does not look so nice from the programming point of view..
	 * @return
	 */
	public EprClause getInstantiationOfClauseForCurrentUnitLiteral() {
		return mInstantiationOfClauseForCurrentUnitLiteral;
	}
	
	
	private void searchUnitLiteral() {
		// that there is exactly one fulfillable literal is a necessary condition for this
		// clause being a unit clause ..
		assert mNoFulfillableLiterals == 1;
		// .. however, it is not a sufficient condition
		//   -- it might be that the reasons for unsatisfiability of the unfulfilled literals,
		//      together with the unfulfilled literals themselves, don't have a unifier
		//      (i.e. in the big conjunction that the quantifier is, there is no single clause
		//       that is unit)
		
		mUnitLiteral = null;
		
		//TODO: this could be done more efficiently i guess..
		for (Literal li : eprQuantifiedPredicateLiterals) {
			if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Unfulfillable) {
				
			} else if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfillable) {
				assert mUnitLiteral == null : "more than one literals are fulfillable -- something's wrong!";
//				if (eprEqualityAtoms.length == 0) {
//					mUnitLiteral = new UnFulReason(li);
//				} else {
					if (li instanceof EprQuantifiedPredicateAtom) {
						mUnitLiteral = //new UnFulReason(
								EprHelpers.buildEQLWE(li.getSign() == 1, 
								(EprQuantifiedPredicateAtom) li.getAtom(), eprEqualityAtoms, this,
								mTheory, mStateManager);
					} else {
						assert false : "TODO -- something about finite models";
					}
//				}
			} else if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfilled) {
				assert false : "the whole clause is fulfilled -- then why should this method be called??";
			} else 
				assert false : "li has no fulfillabilityStatus";
		}
	}
	
		/**
	 * Helper for setting up the clause:
	 * Set the state of euch literal in this clause to fulfilled/fulfillable/unfulfillable
	 * according to the current state stored in the EprStatemanager.
	 */
	private void setLiteralStates() {
		nextLi:
		for (Literal li : eprQuantifiedPredicateLiterals) {

			boolean continueWithNextLiteral = compareToSetQuantifiedLiterals(li);
			if (continueWithNextLiteral)
				continue nextLi;

			EprQuantifiedPredicateAtom liAtom = (EprQuantifiedPredicateAtom) li.getAtom();
			boolean liPositive = li.getSign() == 1;
			// we only reach here if none of the quantified literals in the current state 
			//  fulfilled or contradicted li
			HashSet<TermTuple> otherPolarityPoints = mStateManager.getPoints(!liPositive, liAtom.eprPredicate);
			for (TermTuple opPoint : otherPolarityPoints) { // TODO: seems awfully inefficient..
				if (opPoint.match(liAtom.getArgumentsAsTermTuple(), mEqualityManager) != null) {
//				if (opPoint.match(liAtom.getArgumentsAsTermTuple()) != null) {
					EprGroundPredicateAtom opAtom = liAtom.eprPredicate.getAtomForPoint(opPoint);
					Literal opLit = liPositive ? opAtom.negate() : opAtom;
					setLiteralUnfulfillable(li, 
//							new UnFulReason(liPositive ? opAtom.negate() : opAtom));
							new EprGroundUnitClause(opLit, mTheory, mStateManager, null));
					continue nextLi;
				}
			}
			
			//TODO: can a quantifiedLiteral be fulfilled by enough points???
			// --> in principle yes .. depends on the model .. not sure .. do we need to account for that here?
			
			//if nothing said otherwise, li is fulfillable
			setLiteralFulfillable(li);
		}
		

		for (Literal li : groundLiterals) {
			DPLLAtom liAtom = li.getAtom();
			boolean liPositive = li.getSign() == 1;
			if (liAtom.getDecideStatus() == li) {
				setLiteralFulfilled(li);
			} else if (liAtom.getDecideStatus() == li.negate()) {
				setLiteralUnfulfillable(li, 
						new EprGroundUnitClause(li, mTheory, mStateManager, null));
			} else { //atom is undecided on the DPLL-side (maybe DPLLEngine does not know it??
				if (liAtom instanceof EprGroundPredicateAtom) {
					
					// compare to set quantified literals
					boolean continueWithNextLiteral = compareToSetQuantifiedLiterals(li);
					if (continueWithNextLiteral)
						continue;

					EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) liAtom;
					// compare to points
					HashSet<TermTuple> samePolarityPoints = mStateManager.getPoints(liPositive, 
							egpa.eprPredicate);
					if (samePolarityPoints.contains(egpa.getArgumentsAsTermTuple())) {//TODO: seems inefficient..
//							assert false : "if this is reachable there are "
//									+ "ground atoms that are not known to DPLLEngine - "
//									+ "not necessarily bad, but good to know, maybe..";
							setLiteralFulfilled(li);
							continue;
					}
					HashSet<TermTuple> otherPolarityPoints = mStateManager.getPoints(liPositive, 
							((EprGroundPredicateAtom) liAtom).eprPredicate);
					if (otherPolarityPoints.contains(egpa.getArgumentsAsTermTuple())) {//TODO: seems inefficient..
//						assert false : "if this is reachable there are "
//									+ "ground atoms that are not known to DPLLEngine - "
//									+ "not necessarily bad, but good to know, maybe..";
					EprGroundPredicateAtom opAtom = ((EprGroundPredicateAtom) liAtom).
							eprPredicate.getAtomForPoint(
									egpa.getArgumentsAsTermTuple());
					Literal opLit = liPositive ? opAtom.negate() : opAtom;
						setLiteralUnfulfillable(li, 
								new EprGroundUnitClause(opLit, mTheory, mStateManager, null));
						continue;
					}

				}
				setLiteralFulfillable(li);
			}
		}
		
//		for (Literal l : this.eprEqualityLiterals) {
//			setLiteralUnfulfillable(l, null); //"quantifed equality literal --> we don't track its fulfillability for itself, "
//					//+ "but through handling quantified epr predicate accordingly");
//		}
		
		assert this.getLiteralSet().containsAll(mFulfillabilityStatus.keySet())	&& 
		mFulfillabilityStatus.keySet().containsAll(this.getLiteralSet()) :
			"Fulfillability status map is incomplete.";
	}
	
		/**
	 * Given li, a quantified literal of this clause, which uses an uninterpreted predicate, 
	 * set the status of li to fulfilled/fulfillable/unfulfillable according to which 
	 * quantified literals are set in the current state (as known to the EprStateManager). 
	 * 
	 * If li conflicts with a set quantified literal, do resolution, and add the new clause
	 * to the derived clauses.
	 * 
	 * @param li the literal to set the status of
	 * @return true if the state of li was set because of, false if the quantified literals
	 *           in the current state are indifferent to li
	 */
	private boolean compareToSetQuantifiedLiterals(Literal li) {
		EprQuantifiedPredicateAtom liAtom = (EprQuantifiedPredicateAtom) li.getAtom();
		boolean liPositive = li.getSign() == 1;

		for (EprQuantifiedLitWExcptns sl : mStateManager.getSetLiterals(liAtom.eprPredicate)) {
			TermTuple liTT = liAtom.getArgumentsAsTermTuple();
			TermTuple slTT = sl.getPredicateAtom().getArgumentsAsTermTuple();
			TTSubstitution sub = liTT.match(slTT, mEqualityManager);
			if (sub == null)
				continue;
//			if (subset(sl.mExceptedPoints, this.mExceptedPoints)) { // is this an efficient solution? --> then mb bring it back some time
			
		
			if ((sl.getPredicateLiteral().getSign() == 1) == liPositive) {
				assert false : "TODO..";
			} else {
				EprQuantifiedLitWExcptns liEQLWE = 
					EprHelpers.buildEQLWE(liPositive, 
							liAtom, 
							eprEqualityAtoms, null, //explanation should not be used..
							mTheory, mStateManager);
				EprClause resolvent  = 
						sl.resolveAgainst(liEQLWE, sub);
				
				if (resolvent.isTautology) {
					// the eqlwe don't affect each other --> do nothing 
				} else if (resolvent.isConflictClause()) {
					setLiteralUnfulfillable(li, sl);
				} else {
					ArrayList<Literal> eeas = new ArrayList<>();
					eeas.addAll(Arrays.asList(resolvent.eprEqualityAtoms));
					eeas.addAll(Arrays.asList(resolvent.groundLiterals));
					assert resolvent.eprQuantifiedPredicateLiterals.length == 0;
					assert resolvent.groundLiterals.length == 0
							|| resolvent.groundLiterals[0] instanceof CCEquality : 
								"the resolvent should only consist of equalities, right???";
					EprNonUnitClause dc = (EprNonUnitClause) this.instantiateClause(li, sub, eeas);
					mStateManager.addDerivedClause(dc);
				}
			}

//				if (sl.mIsPositive == liPositive) {
//					if (sub.isEmpty() || isUnifierJustARenaming(sub, liTT, slTT)) {
//						setLiteralFulfilled(li);
//						return true;
//					}
//				} else {
//					setLiteralUnfulfillable(li, new UnFulReason(sl));
//					if (!isUnifierJustARenaming(sub, liTT, slTT) && doesUnifierChangeTheClause(sub, this)) {
//						EprClause dc = instantiateClause(li, sub);
//						if (!dc.isTautology) {
//							System.out.println("EPRDEBUG (EprClause): " + sl + " is set. Creating clause " + this + 
//									". ==> adding derived clause " + this + "\\" + li + " with unifier " + sub);
//							mStateManager.addDerivedClause(dc); //resolution with the unit-clause {sl}
//						} else {
//							System.out.println("EPRDEBUG (EprClause): not adding tautology: " + dc);
//						}
//					}
//					return true;
//				}
//			}
		}
		return false;
	}
	
		private void setLiteralFulfillable(Literal li) {
		FulfillabilityStatus oldStatus = mFulfillabilityStatus.get(li);
		if (oldStatus == FulfillabilityStatus.Fulfilled)
			mFulfilledLiterals.remove(li);
		mFulfillabilityStatus.put(li, FulfillabilityStatus.Fulfillable);
		mNoFulfillableLiterals++;
		if (mNoFulfillableLiterals == 2) {
			mUnitLiteral = null;
		}
	}

	private void setLiteralFulfilled(Literal li) {
		FulfillabilityStatus oldStatus = mFulfillabilityStatus.get(li);
		mFulfillabilityStatus.put(li, FulfillabilityStatus.Fulfilled);
		mFulfilledLiterals.add(li);
		if (oldStatus == FulfillabilityStatus.Fulfillable) {
			mNoFulfillableLiterals--;
			if (mNoFulfillableLiterals == 1) {
				searchUnitLiteral();
			}
		}
	}
	
//	private void setLiteralUnfulfillable(Literal li, UnFulReason reason) {
	private void setLiteralUnfulfillable(Literal li, EprUnitClause reason) {
		FulfillabilityStatus oldStatus = mFulfillabilityStatus.get(li);
		if (oldStatus == FulfillabilityStatus.Fulfilled)
			mFulfilledLiterals.remove(li);
		mFulfillabilityStatus.put(li, FulfillabilityStatus.Unfulfillable);
		if (oldStatus == FulfillabilityStatus.Fulfillable) {
			mNoFulfillableLiterals--;
			if (mNoFulfillableLiterals == 1) {
				searchUnitLiteral();
			}
		}
		
		HashSet<EprUnitClause> ufr = mLiteralToUnfulfillabilityReasons.get(li);
		if (ufr == null) {
			ufr = new HashSet<>();
			mLiteralToUnfulfillabilityReasons.put(li, ufr);
		}
		ufr.add(reason);
	}
	
	public void setQuantifiedLiteralUnfulfillableBecauseOfGroundLiteral(
			Literal quantifiedLit, Literal reason) {
		assert reason.getAtom() instanceof EprGroundPredicateAtom;
		assert quantifiedLit.getAtom() instanceof EprQuantifiedPredicateAtom;
		setLiteralUnfulfillable(quantifiedLit, 
				new EprGroundUnitClause(reason, mTheory, mStateManager, null));
//		updateLiteralToUnfulfillabilityReasons(quantifiedLit, reason);
	}



	/**
	 * Upgrade the clause state to account for the fact that literal has been set.
	 * @param literal
	 */
	public void setGroundLiteral(Literal literal) {
		for (Literal li : groundLiterals) {
			if (literal.getAtom().equals(li.getAtom())) {
				if (literal.getSign() == li.getSign()) {
					setLiteralFulfilled(li);
				} else {
//					TODO: is this right? -- "li is its own reason, bc coming from setLiteral or so..
					setLiteralUnfulfillable(li, new EprGroundUnitClause(li, mTheory, mStateManager, null));
				}
			}
		}
		
		if (literal.getAtom() instanceof EprGroundPredicateAtom) {
			boolean settingPositive = literal.getSign() == 1;
			EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) literal.getAtom();
			TermTuple point = egpa.getArgumentsAsTermTuple(); 
			EprPredicate pred = egpa.eprPredicate; 

			HashSet<Literal> qo = pred.getQuantifiedOccurences().get(this);
			if (qo != null) {
				for (Literal quantifiedLit : qo) {
					boolean oppositeSigns = (quantifiedLit.getSign() == 1) ^ settingPositive;
					TermTuple otherPoint = new TermTuple(((EprPredicateAtom) quantifiedLit.getAtom()).getArguments());
//					HashMap<TermVariable, Term> subs = point.match(otherPoint);
					TTSubstitution subs = point.match(otherPoint, mEqualityManager);
					if (oppositeSigns && subs != null) {
						setQuantifiedLiteralUnfulfillableBecauseOfGroundLiteral(quantifiedLit, literal);
					}
				}
			}
		}	
	}
	
		/**
	 * Upgrade the clause state to account for the fact that the setting of literal has been reverted/backtracked.
	 * @param literal
	 */
	public void unsetGroundLiteral(Literal literal) {
		for (Literal li : groundLiterals) {
			if (literal.getAtom().equals(li.getAtom())) {
				if (literal.getSign() == li.getSign()) {
					assert mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfilled;
					setLiteralFulfillable(li);
				} else {
					assert mFulfillabilityStatus.get(li) == FulfillabilityStatus.Unfulfillable;
					setLiteralFulfillable(li);
				}
			}
		}
		
		// deal with quantified literals that may have been made unfulfillable by the setting of literal
		//  revert their status if this was the only reason of unfulfillability
		for (Entry<Literal, HashSet<EprUnitClause>> en : mLiteralToUnfulfillabilityReasons.entrySet()) {
//			boolean literalWasContained = false;
			EprUnitClause match = null;
			for (EprUnitClause ufr : en.getValue()) { //TODO not nice..
				if (ufr instanceof EprGroundUnitClause 
						&& ((EprGroundUnitClause) ufr).getLiteral().equals(literal)) {
					match = ufr;
				}
			}
			en.getValue().remove(match);
//			if (literalWasContained 
			if (match != null 
					&& en.getValue().isEmpty()) {
				setLiteralFulfillable(en.getKey());
			}
		}
	}

	/**
	 * @return true if at least one of the literals of this clause is definitely true.
	 */
	public boolean isFulfilled() {
		return !mFulfilledLiterals.isEmpty();
	}

	/**
	 * Update the current state of this clause's literals according to the setting of qLiteral.
	 * (difference to compareToSetQuantifiedLiterals: this is called when we freshly set a 
	 *   quantified literal, the other is called upon creation of the clause)
	 *  - If qLiteral occurs in this clause "as is" (i.e. only trivial unification is needed), 
	 *    this means that we can update the clause in-place, DPLL-style, i.e., update the
	 *    fulfillability-status of the literals, or the whole clause
	 *      (TODO: what if there is no unifier? what about factoring?)
	 *  - If the clause has a literal using the same eprPredicate as qLiteral 
	 *   -- .. and that has an opposite sign, we return a fresh clause that follows 
	 *     through first-order resolution with the unit-clause containing qLiteral
	 *   -- .. and that has the same sign, and qLiteral is more general than the literal
	 *      in this clause, we mark this literal as fulfilled.. (..?) 
	 *        (--> EprTheory will then mark the whole clause fulfilled)
	 *   -- .. and that has the same sign, and qLiteral is -not- more general than the 
	 *      literal in the clause, we do nothing
	 * @param qLiteral
	 * @return a fresh EprClause that follows from first-order resolution with qLiteral
	 */
	public EprClause setQuantifiedLiteral(EprQuantifiedLitWExcptns setEqlwe) {
		boolean setLitPositive = setEqlwe.getPredicateLiteral().getSign() == 1;
		EprQuantifiedPredicateAtom setLitAtom = setEqlwe.getPredicateAtom();
//		HashMap<TermVariable, HashSet<ApplicationTerm>> exceptions = eqlwe.mExceptedPoints;
//		assert exceptions == null || exceptions.isEmpty() : "treat this case!";
		
		ArrayList<Literal> predicateLiterals = new ArrayList<>();
		predicateLiterals.addAll(Arrays.asList(eprQuantifiedPredicateLiterals));
		for (Literal l : groundLiterals) 
			if (l instanceof EprGroundPredicateAtom)
				predicateLiterals.add(l);
		
		for (Literal clauseLit : predicateLiterals) {
			boolean clauseLitPositive = clauseLit.getSign() == 1;
			EprPredicateAtom clauseLitAtom = (EprPredicateAtom) clauseLit.getAtom();
			boolean clauseLitIsQuantified = clauseLitAtom instanceof EprQuantifiedPredicateAtom;

			// do the eprPredicates match? do nothing if they don't
			if (!clauseLitAtom.eprPredicate.equals(setLitAtom.eprPredicate)) 
				continue;

			// is there a unifier?
			TermTuple atomArgs = setLitAtom.getArgumentsAsTermTuple();
			TermTuple otherArgs = clauseLitAtom.getArgumentsAsTermTuple();
			TTSubstitution sub = otherArgs.match(atomArgs, mEqualityManager);

			// if there is no unifier, do nothing
			if (sub == null)
				continue;

			if (clauseLitPositive == setLitPositive) {
				assert false : "TODO..";
			} else {
				EprClause resolvent  = null;
				if (clauseLitIsQuantified) {
					EprQuantifiedLitWExcptns liEQLWE = 
							EprHelpers.buildEQLWE(clauseLitPositive, (EprQuantifiedPredicateAtom) clauseLitAtom, 
									eprEqualityAtoms, null,//explanation should not be used..
									mTheory, mStateManager);
					resolvent  = 
							setEqlwe.resolveAgainst(liEQLWE, sub);
				} else {
					resolvent  = 
							setEqlwe.resolveAgainst(clauseLitAtom, sub);
				}
				
				
				if (resolvent.isTautology) {
					// the eqlwe don't affect each other --> do nothing 
				} else if (resolvent.isConflictClause()) {
					setLiteralUnfulfillable(clauseLit, setEqlwe);
				} else {
					ArrayList<Literal> eeas = new ArrayList<>();
					eeas.addAll(Arrays.asList(resolvent.eprEqualityAtoms));
					EprNonUnitClause dc = (EprNonUnitClause) this.instantiateClause(clauseLit, sub, eeas);
					mStateManager.addDerivedClause(dc);
				}
			}
//			// if the unifier is trivial, update this clauses' satisfiability status accordingly
//			boolean unifierTrivial = isUnifierJustARenaming(sub, atomArgs, otherArgs);
//			if (unifierTrivial) {
//				
//				// if the signs match, the clause is fulfilled
//				if (positive == otherPositive
//						&& otherIsQuantified) {
//					setLiteralFulfillable(otherLit);
////					assert !mFulfilledLiterals.contains(otherAtom);
//					mFulfilledLiterals.add(otherLit);
//				} else if (positive != otherPositive
//						&& otherIsQuantified) {
//					setLiteralUnfulfillable(otherLit, new UnFulReason(positive ? atom : atom.negate()));
////					assert !mFulfilledLiterals.contains(otherAtom);
//				} else if (positive == otherPositive
//						&& !otherIsQuantified) {
//					setGroundLiteral(otherLit);
//				} else {
//					setLiteralFulfillable(otherLit);
//				}
//				//TODO: deal with the case where several literals have the same predicate as qLiteral (factoring, multiple resolutions, ..?)
//			}
//
//			//resolution is possible if the signs don't match
//			Literal  skippedLit = positive != otherPositive ? otherLit : null;
//			
//			// if the unifier is not trivial the new clause is different --> return it
//			if (!unifierTrivial || skippedLit != null) {
////				EprClause newClause = instantiateClause(skippedLit, sub);
//				EprClause newClause = instantiateClause(skippedLit, sub);
//				mStateManager.addDerivedClause(newClause);
//				return newClause;
//			}
//			
//			// if this became a conflict clause, we need to return it
//			if (this.isConflictClause()) {
//				return this;
//			}
		}
		return null;
	}
	
	public boolean isConflictClause() {
		for (Entry<Literal, FulfillabilityStatus> en : mFulfillabilityStatus.entrySet())
			if (en.getValue() != FulfillabilityStatus.Unfulfillable)
				return false;
		return true;
	}
}
