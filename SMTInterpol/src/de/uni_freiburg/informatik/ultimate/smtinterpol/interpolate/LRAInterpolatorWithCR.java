/*
 * Copyright (C) 2017 University of Freiburg
 * Copyright (C) 2017 Tanja Schindler
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Vector;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

/**
 * An alternative Interpolator for pure linear arithmetic over the reals. No support of theory combination for now.
 * After calculating an interpolant based on Farkas' coefficients, we use Conflict Resolution to obtain an alternative
 * interpolant.
 * 
 * @author Tanja Schindler
 */
public class LRAInterpolatorWithCR {

	Interpolator mInterpolator;
	Theory mTheory;
	int mNumInterpolants;
	Set<Term>[] mInterpolants;
	Interpolant[] mOldInterpolants;

	Term[] mFarkasInterpolants;
	Set<Term>[] mInitialAConstraints;
	Vector<Term>[] mOrderedVars;
	int[] mFirstAVar;

	@SuppressWarnings("unchecked")
	public LRAInterpolatorWithCR(Interpolator interpolator) {
		mInterpolator = interpolator;
		mTheory = interpolator.mTheory;
		mNumInterpolants = interpolator.mNumInterpolants;
		mInterpolants = new Set[interpolator.mNumInterpolants];
		mOldInterpolants = new Interpolant[interpolator.mNumInterpolants];
		mInitialAConstraints = new Set[interpolator.mNumInterpolants];
		mOrderedVars = new Vector[interpolator.mNumInterpolants];
		for (int i = 0; i < interpolator.mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<Term>();
			mOldInterpolants[i] = new Interpolant();
			mInitialAConstraints[i] = new HashSet<Term>();
			mOrderedVars[i] = new Vector<Term>();
		}
		mFarkasInterpolants = new Term[interpolator.mNumInterpolants];
		mFirstAVar = new int[interpolator.mNumInterpolants];
	}

	/**
	 * Compute partial interpolants for an LA lemma.
	 * 
	 * @param lemma
	 *            the lemma (AnnotatedTerm) for which the partial interpolant is computed.
	 * @return an array containing the partial tree interpolants.
	 */
	public Interpolant[] computeInterpolants(Term lemma) {
		Set<Term>[] constraints = computeFarkasInterpolants(lemma);
		Term[] crInterpolants = computeCRInterpolants(constraints);
		Interpolant[] interpolants = new Interpolant[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			interpolants[color] = new Interpolant(crInterpolants[color]);
		}
		return interpolants;
	}

	/* The Farkas' coefficients based interpolation part */

	/**
	 * Compute the interpolants for this lemma based on Farkas' coefficients, while collecting the constraints needed
	 * for the Conflict Resolution based interpolants.
	 * 
	 * TODO Store only the constraints for color < mNumInterpolants.
	 * 
	 * TODO This is mostly copied. Check what is needed.
	 * 
	 * @param lemma
	 *            The LA lemma (LRA only)
	 * @return for each partition the set of constraints in A in the form <code>linVar <> 0</code> where
	 *         <code><> \in {=, <=, <}</code>.
	 */
	private Set<Term>[] computeFarkasInterpolants(Term lemma) {
		@SuppressWarnings("unchecked")
		Set<Term>[] constraints = new Set[mNumInterpolants + 1];
		for (int color = 0; color < mNumInterpolants + 1; color++) {
			constraints[color] = new HashSet<Term>();
		}

		final Term[] farkasInterpolants = new Term[mNumInterpolants + 1];
		final InterpolatorAffineTerm[] ipl = new InterpolatorAffineTerm[mNumInterpolants + 1];
		for (int color = 0; color < ipl.length; color++) {
			ipl[color] = new InterpolatorAffineTerm();
		}

		@SuppressWarnings("unchecked")
		final ArrayList<TermVariable>[] auxVars = new ArrayList[mNumInterpolants];

		/*
		 * Add the A-part of the literals in this LA lemma.
		 */
		InterpolatorClauseTermInfo mLemmaInfo = mInterpolator.getClauseTermInfo(lemma);

		for (final Entry<Term, Rational> entry : mLemmaInfo.getFarkasCoeffs().entrySet()) {
			final Term lit = mInterpolator.mTheory.not(entry.getKey());
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(lit);
			final Rational factor = entry.getValue();

			assert litTermInfo.isBoundConstraint() || !litTermInfo.isNegated();

			InfinitNumber bound;
			InterpolatorAffineTerm lv;
			if (litTermInfo.isBoundConstraint()) {
				assert factor.signum() == (litTermInfo.isNegated() ? -1 : 1);
				bound = new InfinitNumber(litTermInfo.getBound(), 0);
				// adapt the bound value for strict inequalities
				if (((ApplicationTerm) litTermInfo.getAtom()).getFunction().getName().equals("<")) {
					bound = bound.sub(litTermInfo.getEpsilon());
				}
				// get the inverse bound for negated literals
				if (litTermInfo.isNegated()) {
					bound = bound.add(litTermInfo.getEpsilon());
				}
				lv = litTermInfo.getLinVar();
			} else { // Equality
				assert litTermInfo.isLAEquality();
				lv = litTermInfo.getLinVar();
				bound = new InfinitNumber(litTermInfo.getBound(), 0);
			}
			final LitInfo info = mInterpolator.getLiteralInfo(litTermInfo.getAtom());

			int color = info.mInB.nextClearBit(0);
			while (color < ipl.length) {
				if (info.isMixed(color)) {
					/* ab-mixed interpolation */
					assert (info.mMixedVar != null);
					InterpolatorAffineTerm aPart = new InterpolatorAffineTerm(info.getAPart(color));
					aPart = aPart.add(Rational.MONE, info.mMixedVar);
					ipl[color].add(factor, aPart);

					if (auxVars[color] == null) {
						auxVars[color] = new ArrayList<TermVariable>();
					}
					auxVars[color].add(info.mMixedVar);

					/* Store it to reuse it in the CR part */
					if (litTermInfo.isBoundConstraint()) {
						constraints[color].add(buildConstraint(aPart.mul(factor), false));
					} else { // Equality
						constraints[color].add(buildConstraint(aPart.mul(factor), true));
					}
				}
				if (info.isALocal(color)) {
					/* Literal in A: add to sum */
					InterpolatorAffineTerm aPart = new InterpolatorAffineTerm(lv);
					aPart = aPart.add(bound.negate());
					ipl[color].add(factor, aPart);

					/* Store it to reuse it in the CR part */
					if (litTermInfo.isBoundConstraint()) {
						constraints[color].add(buildConstraint(aPart.mul(factor), false));
					} else { // Equality
						constraints[color].add(buildConstraint(aPart.mul(factor), true));
					}
				}
				color++;
			}
		}
		assert (ipl[ipl.length - 1].isConstant() && InfinitNumber.ZERO.less(ipl[ipl.length - 1].getConstant()));

		/*
		 * Save the interpolants computed for this leaf into the result array.
		 */
		for (int color = 0; color < auxVars.length; color++) {
			final Rational normFactor = ipl[color].isConstant() ? Rational.ONE : ipl[color].getGCD().inverse().abs();
			ipl[color].mul(normFactor);
			/*
			 * Round up the (negated) constant if all terms in the interpolant are known to be integer. This is sound
			 * since x <= 0 is equivalent to ceil(x) <= 0.
			 */
			if (ipl[color].isInt()) {
				ipl[color].mConstant = ipl[color].getConstant().ceil();
			}

			if (auxVars[color] != null) { // NOPMD
				/*
				 * This is a mixed interpolant with auxiliary variables. Prepare an LATerm that wraps the interpolant.
				 */
				InfinitNumber k;
				Term F;
				/* The inequalities are mixed. */
				if (ipl[color].isInt()) {
					k = InfinitNumber.ONE.negate();
				} else {
					k = InfinitNumber.EPSILON.negate();
				}
				F = ipl[color].toLeq0(mTheory);
				final LATerm laTerm = new LATerm(ipl[color], k, F);
				mOldInterpolants[color].mTerm = laTerm;
				// TODO Compare old interpolants with new interpolants to find out how to build the LATerm later.
				farkasInterpolants[color] = buildConstraint(ipl[color], false);
			} else {
				mOldInterpolants[color].mTerm = ipl[color].toLeq0(mTheory);
				farkasInterpolants[color] = buildConstraint(ipl[color], false);
			}
		}
		mFarkasInterpolants = farkasInterpolants;
		return constraints; // TODO Should they be returned as InterpolatorAffineTerm only?
	}

	/* The Conflict Resolution based interpolation part */

	/**
	 * Compute an alternative interpolant by applying conflict resolution on the A part of the problem and the negated
	 * Farkas-based interpolant and storing "interesting" conjuncts.
	 * 
	 * The conflict resolution part roughly follows the paper [2009] Korovin et al. - Conflict Resolution, but we're
	 * building the assignment gradually.
	 * 
	 * TODO For now, this is done for each partition separately. Can we apply it to all partitions simultaneously?
	 * 
	 * @param constraints
	 *            for each partition the constraints for which the CR-based interpolant is computed.The constraints must
	 *            contain only A-local and shared variables and have to be in the form <code>term <> 0</code> with
	 *            <code> <> \in {<,<=} </code>
	 * @return for each partition an alternative interpolant, a conjunction of constraints.
	 */
	private Term[] computeCRInterpolants(Set<Term>[] constraints) {
		Term[] crInterpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			// Check the initial set of constrains S for \bot (\top).
			// As an LA lemma contains non-redundant information only, the only constraint in S that can be \bot (\top)
			// is the Farkas-based interpolant. This can happen if the complete conflict is in the A (B) part. In this
			// case, the CR based interpolant is also \bot (\top).
			if (mFarkasInterpolants[color].equals(mTheory.mFalse) || mFarkasInterpolants[color].equals(mTheory.mTrue)) {
				crInterpolants[color] = mFarkasInterpolants[color];
				continue;
			}
			// Else, generate the CR-based interpolant.
			computeVariableOrder(constraints[color], color);
			ConflictResolutionEngine crEngine = new ConflictResolutionEngine(mOrderedVars[color]);
			// Add all A constraints collected in the Farkas part
			for (Term constraint : constraints[color]) {
				final Term normalizedConstraint = crEngine.addConstraint(constraint);
				mInitialAConstraints[color].add(normalizedConstraint);
			}
			// Add the negated Farkas interpolant
			if (!(mFarkasInterpolants[color].equals(mTheory.mTrue) || mFarkasInterpolants[color].equals(mTheory.mFalse)) ) {
				crEngine.addConstraint(mTheory.not(mFarkasInterpolants[color]));
			}
			// CR algorithm
			Set<Term> itpConjuncts = crEngine.run(color);
			crInterpolants[color] = mTheory.and(itpConjuncts.toArray(new Term[itpConjuncts.size()]));
		}
		return crInterpolants;
	}

	/**
	 * Order the variables occurring in the constraints for partition color such that x_0 < ... < x_i are shared and
	 * x_{i+1} < ... < x_n are A-local.
	 * 
	 * @param constraints
	 *            a set of LRA constraints over shared and A-local variables
	 * @param color
	 *            the interpolation partition
	 * @return the ordered variables in a vector of terms
	 */
	private void computeVariableOrder(Set<Term> constraints, int color) {
		Vector<Term> aLocalVars = new Vector<Term>();
		Vector<Term> sharedVars = new Vector<Term>();
		Set<Term> processedVars = new HashSet<Term>();
		// Group all variables into A-local and shared variables
		for (Term constraint : constraints) {
			final InterpolatorLiteralTermInfo info = mInterpolator.getLiteralTermInfo(constraint);
			final InterpolatorAffineTerm linVar = info.getLinVar();
			for (Term var : linVar.getSummands().keySet()) {
				if (!processedVars.contains(var)) {
					final Occurrence occur = mInterpolator.getOccurrence(var, null);
					assert occur.isAorShared(color);
					if (occur.isAB(color)) {
						sharedVars.add(var);
					} else {
						aLocalVars.add(var);
					}
					processedVars.add(var);
				}
			}
		}
		// Sort both vectors lexicographically
		Collections.sort(aLocalVars, (a, b) -> a.toString().compareTo(b.toString()));
		Collections.sort(sharedVars, (a, b) -> a.toString().compareTo(b.toString()));
		mFirstAVar[color] = sharedVars.size();
		Vector<Term> orderedVariables = sharedVars;
		for (int i = 0; i < aLocalVars.size(); i++) {
			orderedVariables.add(aLocalVars.get(i));
		}
		mOrderedVars[color] = orderedVariables;
	}

	/* CONFLICT RESOLUTION */

	/**
	 * The conflict resolution engine. Given constraints and an order on the occurring variables, this class contains
	 * all the data structures and methods needed for conflict resolution.
	 */
	class ConflictResolutionEngine {
		/**
		 * The ordered variables (ascending).
		 */
		Vector<Term> mOrderedVars;
		/**
		 * A map from the constraint Terms to the corresponding InterpolatorAffineTerms for easy access to the summands.
		 * It is used for the initial and learned constraints.
		 */
		Map<Term, InterpolatorAffineTerm> mConstraintsWithLHS;
		/**
		 * A map from the constraints to the relational operators =, <=, <
		 */
		Map<Term, String> mConstraintsWithRelOp;
		/**
		 * The information about each level containing bounds and constraints
		 */
		CRLevelInfo[] mLevelInfo;

		public ConflictResolutionEngine(Vector<Term> variables) {
			mOrderedVars = variables;
			mConstraintsWithLHS = new HashMap<Term, InterpolatorAffineTerm>();
			mConstraintsWithRelOp = new HashMap<Term, String>();
			mLevelInfo = new CRLevelInfo[variables.size()];
			for (int k = 0; k < variables.size(); k++) {
				mLevelInfo[k] = new CRLevelInfo();
			}
		}

		/**
		 * Add constraints to the CR engine
		 * 
		 * @param constraint
		 *            a constraint over the given variables that can be negated.
		 * @return the normalized initial constraints
		 */
		private Term addConstraint(Term constraint) {
			InterpolatorAffineTerm constraintLHS = computeLHS(constraint);
			final int k = computeLevel(constraintLHS);
			final Term xk = mOrderedVars.get(k);
			final InterpolatorAffineTerm normalLHS = normalizeForVar(constraintLHS, xk);
			final Term normalConstraint;
			boolean isNeg = false;
			String relOp;
			assert constraint instanceof ApplicationTerm;
			// Get the relational operator.
			if (((ApplicationTerm) constraint).getFunction().getName().equals("not")) {
				isNeg = true;
				constraint = ((ApplicationTerm) constraint).getParameters()[0];
			}
			relOp = ((ApplicationTerm) constraint).getFunction().getName();
			if (relOp == "=") {
				normalConstraint = buildConstraint(normalLHS, true);
			} else {
				assert relOp == "<" || relOp == "<=";
				normalConstraint = buildConstraint(normalLHS, false);
			}
			// Add the normalized constraints to the data structures for the CR engine
			mConstraintsWithLHS.put(normalConstraint, normalLHS);
			if (isNeg) {
				relOp = ((ApplicationTerm) normalConstraint).getFunction().getName();
			}
			mConstraintsWithRelOp.put(normalConstraint, relOp);
			mLevelInfo[k].mConstraints.add(normalConstraint);
			return normalConstraint;
		}

		/**
		 * Run the CR algorithm given a set of constraints and an order on the occurring variables.
		 * 
		 * @return The interpolant conjuncts
		 */
		private Set<Term> run(int color) {
			Set<Term> itpConjuncts = new HashSet<Term>();
			boolean done = false;
			for (int k = 0; !done && k < mOrderedVars.size(); k++) {
				recalculateBounds(k);
				if (!isInConflict(k)) {
					updateAssignment(k);
				} else {
					while (!done && isInConflict(k)) {
						// Add the parent constraints to the interpolant if they were initial constraints over shared
						// vars
						final int parentK = k;
						final Term parent = mLevelInfo[parentK].mLBConstraint;
						final Term otherParent = mLevelInfo[parentK].mUBConstraint;
						if (parentK < mFirstAVar[color]) {
							if (mInitialAConstraints[color].contains(parent)) {
								itpConjuncts.add(parent);
							}
							if (mInitialAConstraints[color].contains(otherParent)) {
								itpConjuncts.add(otherParent);
							}
						}
						// Resolve
						final InterpolatorAffineTerm resLHS = resolveConflict(k); // (CR)
						k = computeLevel(resLHS); // k := the level of the resolvent. It is -1 if no variable occurs.
						if (k != -1) {
							final Term resolvent = addLearnedConstraint(resLHS, k, parentK);
							updateBounds(k, resolvent);
							// Add the resolvent to the interpolant if the parents had A-local vars and the resolvent
							// not.
							if (k < mFirstAVar[color] && parentK >= mFirstAVar[color]) {
								itpConjuncts.add(resolvent);
							}
						} else { // if k = -1 then we are done
							done = true;
						}
					}
					if (!done) {
						updateAssignment(k); // xk->v, where v is a value satisfying all constraints of level <= k (AR)
					}
				}
			}
			return itpConjuncts;
		}

		/* Main steps in the CR algorithm */
		/**
		 * Recalculate the bounds for a variable using all constraints of the level.
		 * 
		 * @param k
		 *            the level.
		 */
		private void recalculateBounds(int k) {
			// Reset bounds
			mLevelInfo[k].mLowerBound = InfinitNumber.NEGATIVE_INFINITY;
			mLevelInfo[k].mUpperBound = InfinitNumber.POSITIVE_INFINITY;
			// Recalculate using all constraints
			for (Term constraint : mLevelInfo[k].mConstraints) {
				updateBounds(k, constraint);
			}
		}

		/**
		 * Update the bounds for a variable using one constraint.
		 * 
		 * @param k
		 *            the level
		 * @param constraint
		 *            the constraint responsible for the bound update
		 */
		private void updateBounds(int k, Term constraint) {
			final Term xk = mOrderedVars.get(k);
			final InterpolatorAffineTerm constraintLHS = mConstraintsWithLHS.get(constraint);
			final Rational factor = constraintLHS.getSummands().get(xk);
			final InterpolatorAffineTerm lhsWithoutXk =
					new InterpolatorAffineTerm(constraintLHS).add(factor.negate(), xk);
			InfinitNumber bound = evaluateTerm(lhsWithoutXk);
			if (factor.isNegative()) {
				if (!bound.lesseq(mLevelInfo[k].mLowerBound)) {
					mLevelInfo[k].mLowerBound = bound;
					mLevelInfo[k].mLBConstraint = constraint;
				}
				// For an equality, we have to update the upper bound if the new value is less
				if (mConstraintsWithRelOp.get(constraint) == "=" && bound.less(mLevelInfo[k].mUpperBound)) {
					mLevelInfo[k].mUpperBound = bound;
					mLevelInfo[k].mUBConstraint = constraint;
				}
			} else {
				bound = bound.negate();
				if (bound.less(mLevelInfo[k].mUpperBound)) {
					mLevelInfo[k].mUpperBound = bound;
					mLevelInfo[k].mUBConstraint = constraint;
				}
				// For an equality, we have to update the lower bound if the new value is greater
				if (mConstraintsWithRelOp.get(constraint) == "=" && !bound.lesseq(mLevelInfo[k].mLowerBound)) {
					mLevelInfo[k].mLowerBound = bound;
					mLevelInfo[k].mLBConstraint = constraint;
				}
			}
		}

		/**
		 * Check if there is a conflict, i.e. if a variable's lower bound is greater than its upper bound.
		 * 
		 * @param k
		 *            the level.
		 */
		private boolean isInConflict(int k) {
			return mLevelInfo[k].mUpperBound.less(mLevelInfo[k].mLowerBound);
		}

		/**
		 * Resolve the conflict in the given level.
		 * 
		 * @param k
		 *            the level.
		 * @return the resolvent's lhs
		 */
		private InterpolatorAffineTerm resolveConflict(int k) {
			assert mLevelInfo[k].mUpperBound.less(mLevelInfo[k].mLowerBound);
			final Term topVar = mOrderedVars.get(k);
			final Term lowerConstraint = mLevelInfo[k].mLBConstraint;
			final Term upperConstraint = mLevelInfo[k].mUBConstraint;
			final InterpolatorAffineTerm lowerLHS = mConstraintsWithLHS.get(lowerConstraint);
			final InterpolatorAffineTerm upperLHS = mConstraintsWithLHS.get(upperConstraint);
			final InterpolatorAffineTerm resolventLHS;

			// In case we have an equality in one constraint, we have to multiply it by -1 if the top variable has the
			// same sign in the other constraint
			if (mConstraintsWithRelOp.get(lowerConstraint) == "=") {
				if (lowerLHS.getSummands().get(topVar).equals(upperLHS.getSummands().get(topVar))) {
					resolventLHS = new InterpolatorAffineTerm(upperLHS).add(Rational.MONE, lowerLHS);
				} else {
					resolventLHS = new InterpolatorAffineTerm(upperLHS).add(Rational.ONE, lowerLHS);
				}
			} else if (mConstraintsWithRelOp.get(upperConstraint) == "=") {
				if (upperLHS.getSummands().get(topVar).equals(lowerLHS.getSummands().get(topVar))) {
					resolventLHS = new InterpolatorAffineTerm(lowerLHS).add(Rational.MONE, upperLHS);
				} else {
					resolventLHS = new InterpolatorAffineTerm(lowerLHS).add(Rational.ONE, upperLHS);
				}
			} else { // A conflict between two term <(=) 0 requires coeffs +1 and -1
				resolventLHS = new InterpolatorAffineTerm(lowerLHS).add(Rational.ONE, upperLHS);
			}
			return resolventLHS;
		}

		/**
		 * Compute the level of a constraint.
		 * 
		 * @param lhs
		 *            The lhs of a constraint of form <code>term <= 0</code>
		 * @return The number of the top variable, or -1 if the lhs is a constant
		 */
		private int computeLevel(InterpolatorAffineTerm lhs) {
			if (lhs.getSummands().isEmpty()) {
				return -1;
			} else {
				int level = 0;
				for (Term xk : lhs.getSummands().keySet()) {
					final int k = mOrderedVars.indexOf(xk);
					if (k > level) {
						level = k;
					}
				}
				return level;
			}
		}

		/**
		 * Update the assignment for variable x_k by a value such that all constraints of level k are satisfied.
		 */
		private void updateAssignment(int k) {
			final InfinitNumber lowerBound = mLevelInfo[k].mLowerBound;
			final InfinitNumber upperBound = mLevelInfo[k].mUpperBound;
			if (lowerBound.equals(InfinitNumber.NEGATIVE_INFINITY)
					&& upperBound.equals(InfinitNumber.POSITIVE_INFINITY)) {
				mLevelInfo[k].mVarAssignment = Rational.ZERO;
			} else if (lowerBound.equals(InfinitNumber.NEGATIVE_INFINITY)) {
				mLevelInfo[k].mVarAssignment = upperBound.mA.sub(Rational.ONE);
			} else if (upperBound.equals(InfinitNumber.POSITIVE_INFINITY)) {
				mLevelInfo[k].mVarAssignment = lowerBound.mA.add(Rational.ONE);
			} else {
				mLevelInfo[k].mVarAssignment = upperBound.mA.add(lowerBound.mA).div(Rational.TWO);
			}
		}

		/* Helpers */
		/**
		 * Store all the information about a level needed for the CR algorithm. This is: (1) the constraints of this
		 * level, (2) the current assignment of the top variable, (3) the lower and upper bounds and the responsible
		 * constraints.
		 */
		class CRLevelInfo {
			Set<Term> mConstraints;
			Rational mVarAssignment;
			InfinitNumber mLowerBound, mUpperBound;
			Term mLBConstraint, mUBConstraint;

			public CRLevelInfo() {
				mConstraints = new HashSet<Term>();
				mVarAssignment = null;
				mLowerBound = InfinitNumber.NEGATIVE_INFINITY;
				mUpperBound = InfinitNumber.POSITIVE_INFINITY;
				mLBConstraint = null;
				mUBConstraint = null;
			}
		}

		/**
		 * Normalize the lhs of a constraint such that the top variable x_k has coefficient +-1.
		 */
		private InterpolatorAffineTerm normalizeForVar(InterpolatorAffineTerm affineTerm, Term topVar) {
			final Rational coeff = affineTerm.getSummands().get(topVar);
			Rational factor = coeff;
			if (factor.isNegative()) {
				factor = factor.negate();
			}
			return new InterpolatorAffineTerm(affineTerm).div(factor);
		}

		/**
		 * Evaluate a term under the current assignment.
		 */
		private InfinitNumber evaluateTerm(InterpolatorAffineTerm constraintLHS) {
			InfinitNumber evaluated = new InfinitNumber();
			for (final Term var : constraintLHS.getSummands().keySet()) {
				final int k = mOrderedVars.indexOf(var);
				final Rational coeff = constraintLHS.getSummands().get(var);
				final Rational value = mLevelInfo[k].mVarAssignment;
				evaluated = evaluated.addmul(InfinitNumber.ONE, coeff.mul(value));
			}
			evaluated = evaluated.add(constraintLHS.getConstant());
			return evaluated;
		}

		/**
		 * Add a learned constraint: Normalize it and add it to the internal data structures.
		 * 
		 * @param constraintLHS
		 *            The left hand side of the new constraint
		 * @param level
		 *            The level of the new constraint
		 * @return The normalized constraint in the form "+-x_k + term <= 0" where x_k is the top variable.
		 */
		private Term addLearnedConstraint(InterpolatorAffineTerm constraintLHS, int k, int parentK) {
			final Term topVar = mOrderedVars.get(k);
			final InterpolatorAffineTerm normalLHS = normalizeForVar(constraintLHS, topVar);
			final String firstRelOp = mConstraintsWithRelOp.get(mLevelInfo[parentK].mLBConstraint);
			final String secondRelOp = mConstraintsWithRelOp.get(mLevelInfo[parentK].mUBConstraint);
			final Term normalConstraint;
			final String relOp;
			if (firstRelOp == "=" && secondRelOp == "=") {
				normalConstraint = buildConstraint(normalLHS, true);
				relOp = "=";
			} else {
				normalConstraint = buildConstraint(normalLHS, false);
				relOp = ((ApplicationTerm) normalConstraint).getFunction().getName();
			}
			mConstraintsWithLHS.put(normalConstraint, normalLHS);
			mConstraintsWithRelOp.put(normalConstraint, relOp);
			mLevelInfo[k].mConstraints.add(normalConstraint);
			return normalConstraint;
		}
	}

	/**
	 * Collect the left hand side of a constraint of form <code>term <> 0</code> with <code> <> \in {=,<=,<}</code>
	 * 
	 * @param constraint
	 *            a LRA constraint
	 * @return the LHS of the constraint
	 */
	private InterpolatorAffineTerm computeLHS(Term constraint) {
		final InterpolatorAffineTerm leq0Lhs;
		final InterpolatorLiteralTermInfo info = mInterpolator.getLiteralTermInfo(constraint);
		Rational negationFactor = Rational.ONE;
		if (info.isNegated()) {
			negationFactor = Rational.MONE;
		}
		final InterpolatorAffineTerm linVar = info.getLinVar();
		InfinitNumber bound = new InfinitNumber(info.getBound(), 0);
		// Get the inverse bound for negated literals
		if (info.isNegated()) {
			bound = bound.add(info.getEpsilon());
		}
		// Adapt the bound value for strict inequalities
		if (((ApplicationTerm) info.getAtom()).getFunction().getName().equals("<")) {
			bound = bound.sub(info.getEpsilon());
		}
		leq0Lhs = new InterpolatorAffineTerm(linVar.mul(negationFactor)).add(bound.negate().mul(negationFactor));
		return leq0Lhs;
	}

	/**
	 * Create a constraint of form <code>term <> 0</code> from the lhs where <code><>\in{<,<=,=}</code>
	 * 
	 * @param lhs
	 *            the left side of the constraint
	 * @param isEq
	 *            determines if the constraint is an equality (true) or inequality (false)
	 * @return the constraint term of form <code>term <> 0</code>
	 */
	private Term buildConstraint(InterpolatorAffineTerm lhs, boolean isEq) {
		if (lhs.isConstant()) {
			return lhs.getConstant().compareTo(InfinitNumber.ZERO) <= 0 ? mTheory.mTrue : mTheory.mFalse;
		}
		final Sort sort = mTheory.getSort("Real");
		final InfinitNumber constant = lhs.getConstant();
		final Term constTerm = constant.mA.equals(Rational.ZERO) ? null : constant.mA.toTerm(sort);
		final Term[] subTerms = new Term[lhs.getSummands().size() + (constTerm == null ? 0 : 1)];
		int index = 0;
		for (Entry<Term, Rational> sum : lhs.getSummands().entrySet()) {
			final Term var = sum.getKey();
			final Term factor = sum.getValue().toTerm(sort);
			subTerms[index++] = mTheory.term("*", factor, var);
		}
		if (constTerm != null) {
			subTerms[index] = constTerm;
		}
		final Term lhsTerm = subTerms.length == 1 ? subTerms[0] : mTheory.term("+", subTerms);
		// final Term lhsTerm = lhs.toSMTLib(mTheory, isInt); // TODO Use this if toSMTLib stops building nested sums
		final Term zero = Rational.ZERO.toTerm(sort);
		final Term constraint;
		if (isEq) {
			constraint = mTheory.term("=", lhsTerm, zero);
		} else {
			if (lhs.getConstant().mEps != 0) {
				constraint = mTheory.term("<", lhsTerm, zero);
			} else {
				constraint = mTheory.term("<=", lhsTerm, zero);
			}
		}
		return constraint;
	}
}
