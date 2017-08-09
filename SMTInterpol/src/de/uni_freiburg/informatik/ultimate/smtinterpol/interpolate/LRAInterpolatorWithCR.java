package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * An alternative Interpolator for pure linear arithmetic over the reals. No support of theory combination for now.
 * After calculating an interpolant based on Farkas' coefficients, we use Conflict Resolution to obtain an alternative
 * interpolant.
 * 
 * TODO For now, it can only deal with inequalities (where all are brought to non-strict form. Use InfinitNumber to
 * transform strict into non-strict). No equalities and disequalities supported (to be implemented).
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

	@SuppressWarnings("unchecked")
	public LRAInterpolatorWithCR(Interpolator interpolator) {
		mInterpolator = interpolator;
		mTheory = interpolator.mTheory;
		mNumInterpolants = interpolator.mNumInterpolants;
		mInterpolants = new Set[interpolator.mNumInterpolants];
		mOldInterpolants = new Interpolant[interpolator.mNumInterpolants];
		mInitialAConstraints = new Set[interpolator.mNumInterpolants];
		for (int i = 0; i < interpolator.mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<Term>();
			mOldInterpolants[i] = new Interpolant();
			mInitialAConstraints[i] = new HashSet<Term>();
		}
		mFarkasInterpolants = new Term[interpolator.mNumInterpolants];
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
	 * TODO Store only the constraints for color < mNumInterpolants. TODO This is mostly copied. Check what is needed.
	 * 
	 * @param lemma
	 *            The LA lemma (LRA only)
	 * @return for each partition the set of constraints in A in the form <code>linVar <> 0</code> where
	 *         <code><> \in {<=, <}</code>.
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
		 * these variables are used for trichotomy clauses. The inequalityInfo will remember the information for one of
		 * the inequalities to get the aux literal. The equality will remember the equality literal and equalityInfo
		 * will remember its info.
		 */
//		Term equality = null;
		LitInfo equalityInfo = null;
		Interpolator.Occurrence inequalityInfo = null;

		/*
		 * Add the A-part of the literals in this LA lemma.
		 */
		InterpolatorClauseTermInfo mLemmaInfo = mInterpolator.getClauseTermInfo(lemma);

		for (final Entry<Term, Rational> entry : mLemmaInfo.getFarkasCoeffs().entrySet()) {
			final Term lit = mInterpolator.mTheory.not(entry.getKey());
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(lit);
			final Rational factor = entry.getValue();
			if (litTermInfo.isBoundConstraint() || (!litTermInfo.isNegated() && litTermInfo.isLAEquality())) {
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
				} else {
					// TODO How do we support them?
					throw new IllegalArgumentException("(Dis-)Equalities not yet supported.");
					// assert litTermInfo.isLAEquality();
					// lv = litTermInfo.getLinVar();
					// bound = new InfinitNumber(litTermInfo.getBound(), 0);
				}
				final LitInfo info = mInterpolator.getLiteralInfo(litTermInfo.getAtom());
				inequalityInfo = info;

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
						constraints[color].add(buildTermLeq0(aPart.mul(factor)));
					}
					if (info.isALocal(color)) {
						/* Literal in A: add to sum */
						InterpolatorAffineTerm aPart = new InterpolatorAffineTerm(lv);
						aPart = aPart.add(bound.negate());
						ipl[color].add(factor, aPart);

						/* Store it to reuse it in the CR part */
						constraints[color].add(buildTermLeq0(aPart.mul(factor)));
					}
					color++;
				}
			} else if (litTermInfo.isNegated() && litTermInfo.isLAEquality()) {
				// TODO How do we support them?
				throw new IllegalArgumentException("(Dis-)Equalities not yet supported.");
				// we have a Trichotomy Clause
				// equality = litTermInfo.getAtom();
				// final Term eq = equality;
				// // a trichotomy clause must contain exactly three parts
				// assert mLemmaInfo.getLiterals().size() == 3;// NOCHECKSTYLE
				// assert equalityInfo == null;
				// equalityInfo = mInterpolator.getLiteralInfo(eq);
				// assert factor.abs() == Rational.ONE;
				//
				// int color = equalityInfo.mInB.nextClearBit(0);
				// while (color < ipl.length) {
				// if (equalityInfo.isALocal(color)) {
				// /* Literal in A: add epsilon to sum */
				// ipl[color].add(litTermInfo.getEpsilon());
				//
				// /* Store the literal to reuse it in the CR part */
				// constraints[color].add(lit);
				// }
				// color++;
				// }
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
				if (equalityInfo != null) { // NOPMD
					// TODO How do we support them?
					throw new IllegalArgumentException("(Dis-)Equalities not yet supported.");
					/*
					 * This is a mixed trichotomy clause. This requires a very special interpolant.
					 */
					// assert equalityInfo.isMixed(color);
					// assert auxVars[color].size() == 2;
					// assert normFactor == Rational.ONE;
					// final InterpolatorAffineTerm less =
					// new InterpolatorAffineTerm(ipl[color]).add(InfinitNumber.EPSILON);
					// k = InfinitNumber.ZERO;
					// F = mInterpolator.mTheory.and(ipl[color].toLeq0(mInterpolator.mTheory),
					// mInterpolator.mTheory.or(less.toLeq0(mInterpolator.mTheory), mInterpolator.mTheory
					// .equals(equalityInfo.getMixedVar(), auxVars[color].iterator().next())));
				} else {
					/* Just the inequalities are mixed. */
					if (ipl[color].isInt()) {
						k = InfinitNumber.ONE.negate();
					} else {
						k = InfinitNumber.EPSILON.negate();
					}
					F = ipl[color].toLeq0(mTheory);
				}
				final LATerm laTerm = new LATerm(ipl[color], k, F);
				mOldInterpolants[color].mTerm = laTerm;
				// TODO Compare old interpolants with new interpolants to find out how to build the LATerm later.
				farkasInterpolants[color] = buildTermLeq0(ipl[color]);
			} else {
				assert (equalityInfo == null || !equalityInfo.isMixed(color));
				if (equalityInfo != null && ipl[color].isConstant()
						&& equalityInfo.isALocal(color) != inequalityInfo.isALocal(color)) {
					// TODO How do we support them?
					throw new IllegalArgumentException("(Dis-)Equalities not yet supported.");
					/*
					 * special case: Nelson-Oppen conflict, a <= b and b <= a in one partition, a != b in the other. If
					 * a != b is in A, the interpolant is simply a != b. If a != b is in B, the interpolant is simply a
					 * == b.
					 */
					// final Term thisIpl = equalityInfo.isALocal(color) ? mTheory.not(equality) : equality;
					// mOldInterpolants[color].mTerm = thisIpl;
				} else {
					mOldInterpolants[color].mTerm = ipl[color].toLeq0(mTheory);
					farkasInterpolants[color] = buildTermLeq0(ipl[color]);
				}
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
			final Vector<Term> variables = computeVariableOrder(constraints[color], color);
			ConflictResolutionEngine crEngine = new ConflictResolutionEngine(variables);
			// Add all A constraints collected in the Farkas part
			for (Term constraint : constraints[color]) {
				final Term normalizedConstraint = crEngine.addConstraint(constraint);
				mInitialAConstraints[color].add(normalizedConstraint);
			}
			// Add the negated Farkas interpolant
			crEngine.addConstraint(mTheory.not(mFarkasInterpolants[color]));
			// CR algorithm
			Map<Term, SymmetricPair<Term>> conflicts = crEngine.run();
			Map<Term, Integer> constraintsWithLevel = crEngine.getConstraints();
			// Collect interpolant
			Set<Term> itpConjuncts = computeInterpolantConjuncts(variables, conflicts, constraintsWithLevel, color);
			// Build the interpolant for this partition.
			crInterpolants[color] = mTheory.and(itpConjuncts.toArray(new Term[itpConjuncts.size()]));
		}
		return crInterpolants;
	}

	/**
	 * Order the variables occurring in the constraints for partition color such that x_0 < ... < x_i are shared and
	 * x_{i+1} < ... < x_n are A-local
	 * 
	 * @param constraints
	 *            a set of LRA constraints over shared and A-local variables
	 * @param color
	 *            the interpolation partition
	 * @return the ordered variables in a vector of terms
	 */
	private Vector<Term> computeVariableOrder(Set<Term> constraints, int color) {
		Vector<Term> variables = new Vector<Term>();
		for (Term constraint : constraints) {
			final InterpolatorLiteralTermInfo info = mInterpolator.getLiteralTermInfo(constraint);
			final InterpolatorAffineTerm linVar = info.getLinVar();
			for (Term var : linVar.getSummands().keySet()) {
				if (!variables.contains(var)) {
					final Occurrence occur = mInterpolator.getOccurrence(var, null);
					assert occur.isAorShared(color);
					if (occur.isAB(color)) {
						variables.add(0, var);
					} else {
						variables.add(var);
					}
				}
			}
		}
		return variables;
	}

	/**
	 * Compute the conjuncts for the interpolant: - constraints from the A part of the original problem over shared
	 * variables only, that are used in CR and - resolvents containing only shared variables whose parents contain
	 * A-local variables.
	 * 
	 * @param variables
	 *            The variables ordered from shared to A-local
	 * @param conflicts
	 *            The conflicts from the CR algorithm
	 * @param color
	 *            The partition
	 * @return The interpolant conjuncts for this partition
	 */
	private Set<Term> computeInterpolantConjuncts(Vector<Term> variables, Map<Term, SymmetricPair<Term>> conflicts,
			Map<Term, Integer> constraintsWithLevel, int color) {
		// Compute first A-local variable (if there is one)
		int firstA = variables.size();
		for (int i = 0; i < variables.size(); i++) {
			final Occurrence occur = mInterpolator.getOccurrence(variables.get(i), null);
			if (occur.isALocal(color)) {
				firstA = i;
				break;
			}
		}
		// Filter the constraints for the interpolant.
		Set<Term> itpConjuncts = new HashSet<Term>();
		for (Map.Entry<Term, SymmetricPair<Term>> conflict : conflicts.entrySet()) {
			final Term resolvent = conflict.getKey();
			final Term parent = conflict.getValue().getFirst();
			final Term otherParent = conflict.getValue().getSecond();
			// Add constraints from the original problem if they appear in a conflict and contain shared variables only.
			if (mInitialAConstraints[color].contains(parent)) {
				if (constraintsWithLevel.get(parent) < firstA) {
					itpConjuncts.add(parent);
				}
			}
			if (mInitialAConstraints[color].contains(otherParent)) {
				if (constraintsWithLevel.get(otherParent) < firstA) {
					itpConjuncts.add(otherParent);
				}
			}
			// Add constraints over shared variables if they are resolvents of constraints with A-local variables.
			if (constraintsWithLevel.get(resolvent) < firstA) {
				if (constraintsWithLevel.get(parent) >= firstA && constraintsWithLevel.get(otherParent) >= firstA) {
					itpConjuncts.add(resolvent);
				}
			}
		}
		return itpConjuncts;
	}

	/**
	 * Collect the left hand side of a constraint of form <code>term <= 0</code>
	 * 
	 * @param constraint
	 *            a LRA constraint
	 * @return the LHS of the constraint
	 */
	private InterpolatorAffineTerm computeLHSForLeq0(Term constraint) {
		final InterpolatorAffineTerm leq0Lhs;
		final InterpolatorLiteralTermInfo info = mInterpolator.getLiteralTermInfo(constraint);
		if (info.isBoundConstraint()) {
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
		} else { // Build two inequalities from (dis-)equalities
			throw new IllegalArgumentException("(Dis-)Equalities not yet supported.");
		}
		return leq0Lhs;
	}

	/**
	 * Create a constraint of form <code>term <> 0</code> from the lhs where <code><>\in{<,<=}</code>
	 * 
	 * @param lhs
	 *            the left side of the constraint
	 * @return the constraint term of form <code>term <> 0</code>
	 */
	private Term buildTermLeq0(InterpolatorAffineTerm lhs) {
		final boolean isInt = false; // = lhs.isInt(); TODO Not needed for Rationals, but will we extend this?
		final Sort sort = mTheory.getSort(isInt ? "Int" : "Real");
		// TODO The following is done because InterpolatorAffineTerm.toSMTLib builds nested sums (might be changed in
		// the future) and we cannot deal with them here.
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
		final Term leq0constraint;
		if (lhs.getConstant().mEps != 0) {
			leq0constraint = mTheory.term("<", lhsTerm, zero);
		} else {
			leq0constraint = mTheory.term("<=", lhsTerm, zero);
		}
		return leq0constraint;
	}

	/* CONFLICT RESOLUTION - I made it as independent from anything else as possible. */

	/**
	 * The conflict resolution engine. Given constraints and an order on the occurring variables, this class contains
	 * all the data structures and methods needed for conflict resolution.
	 * 
	 * TODO Rename this.
	 */
	class ConflictResolutionEngine {
		/**
		 * The ordered variables (ascending).
		 */
		Vector<Term> mOrderedVariables;
		/**
		 * A map from the constraint Terms to the corresponding InterpolatorAffineTerms for easy access to the summands.
		 * It is used for the initial and learned constraints.
		 */
		Map<Term, InterpolatorAffineTerm> mConstraints;
		/**
		 * This map stores for each variable the set of constraints where it is the top variable.
		 */
		Map<Term, Set<Term>> mTopVariables;
		/**
		 * Current variable assignment
		 */
		Map<Term, Rational> mAssignments;
		/**
		 * The current conflict
		 */
		SymmetricPair<Term> mConflict;

		public ConflictResolutionEngine(Vector<Term> variables) {
			mOrderedVariables = variables;
			mConstraints = new HashMap<Term, InterpolatorAffineTerm>();
			mTopVariables = new HashMap<Term, Set<Term>>();
			for (Term var : mOrderedVariables) {
				mTopVariables.put(var, new HashSet<Term>());
			}
			mAssignments = new HashMap<Term, Rational>();
			mConflict = null;
		}

		/**
		 * Add constraints to the CR engine
		 * 
		 * @param constraint
		 *            a constraint over the given variables
		 * @return the normalized initial constraints
		 */
		private Term addConstraint(Term constraint) {
			// TODO When dealing with = and !=, this should create a pair of constraints
			InterpolatorAffineTerm constraintLHS = computeLHSForLeq0(constraint);
			final Term topVar = computeTopVar(constraintLHS, mOrderedVariables.size() - 1);
			final InterpolatorAffineTerm normalLHS = normalizeForVar(constraintLHS, topVar);
			final Term normalConstraint = buildTermLeq0(normalLHS);
			// Add the normalized constraints to the data structures for the CR engine
			mTopVariables.get(topVar).add(normalConstraint);
			mConstraints.put(normalConstraint, normalLHS);
			return normalConstraint;
		}

		/**
		 * Run the CR algorithm given a set of constraints and an order on the occurring variables.
		 * 
		 * @return The set of conflicts that have been detected during the run. (Note that it does not contain the
		 *         conlict with resolvent \bot)
		 */
		private Map<Term, SymmetricPair<Term>> run() {
			Map<Term, SymmetricPair<Term>> conflicts = new HashMap<Term, SymmetricPair<Term>>();
			int k = 0;
			outer: // TODO Does it make sense NOT to start with an assignment?
			// TODO Is it easier and/or more efficient to loop over the top variables?
			while (k < mOrderedVariables.size()) {
				while (true) { // while there exists a k-conflict
					final InterpolatorAffineTerm resLHS = detectConflict(k);
					if (resLHS == null) { // There is no conflict
						break;
					}
					k = computeLevel(resLHS, k - 1); // k := the level of the resolvent. It is -1 if no variable occurs.
					if (k == -1) { // if k = -1 then return “unsatisfiable”
						break outer;
					}
					final Term resolvent = addLearnedConstraint(resLHS, k); // (CR)
					conflicts.put(resolvent, mConflict); // Add the conflict to the set of all occurring conflicts
					// TODO Should this be done before "break" in order to get the conflict leading to \bot
				}
				updateAssignment(k); // xk->v, where v is a value satisfying all constraints of level <=k (AR)
				k++;
			}
			return conflicts;
		}

		/* Main steps in the CR algorithm */
		/**
		 * Try to find a conflict in this level.
		 * 
		 * @return the resolvent's lhs
		 */
		private InterpolatorAffineTerm detectConflict(int level) {
			final Term topVar = mOrderedVariables.get(level);
			for (Term constraint : mTopVariables.get(topVar)) {
				final InterpolatorAffineTerm constraintLHS = mConstraints.get(constraint);
				final Rational coeff = constraintLHS.getSummands().get(topVar);
				assert coeff == Rational.ONE || coeff == Rational.MONE;
				// Find a constraint where the top variable has the opposite coefficient
				// TODO This doesn't need to go through all constraints again.
				for (Term other : mTopVariables.get(topVar)) {
					final InterpolatorAffineTerm otherLHS = mConstraints.get(other);
					if (!otherLHS.getSummands().get(topVar).equals(coeff.negate())) {
						continue;
					}
					final InterpolatorAffineTerm resolventLHS =
							new InterpolatorAffineTerm(constraintLHS).add(Rational.ONE, otherLHS);
					final InfinitNumber evaluatedSum = evaluateTerm(resolventLHS);
					if (!evaluatedSum.lesseq(InfinitNumber.ZERO)) {
						mConflict = new SymmetricPair<Term>(constraint, other);
						return resolventLHS;
					}
				}
			}
			return null;
		}

		/**
		 * Compute the level of a constraint.
		 * 
		 * @param lhs
		 *            The lhs of a constraint of form <code>term <= 0</code>
		 * @return The number of the top variable, or -1 if the lhs is a constant
		 */
		private int computeLevel(InterpolatorAffineTerm lhs, int maxLevel) {
			if (lhs.getSummands().isEmpty()) {
				return -1;
			} else {
				int k = maxLevel;
				while (k > 0) {
					final Term var = mOrderedVariables.get(k);
					if (lhs.getSummands().containsKey(var)) {
						break;
					}
					k--;
				}
				return k;
			}
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
		private Term addLearnedConstraint(InterpolatorAffineTerm constraintLHS, int level) {
			final Term topVar = mOrderedVariables.get(level);
			final InterpolatorAffineTerm normalLHS = normalizeForVar(constraintLHS, topVar);
			final Term normalConstraint = buildTermLeq0(normalLHS);
			mTopVariables.get(topVar).add(normalConstraint);
			mConstraints.put(normalConstraint, normalLHS);
			return normalConstraint;
		}

		/**
		 * Update the assignment for variable x_k by a value such that all constraints of level k are satisfied. Also,
		 * remove all assignments for variables x_i > x_k unless x_k was assigned for the first time.
		 * 
		 * TODO Do we need the latter? At the moment not.
		 */
		private void updateAssignment(int k) {
			final Term xk = mOrderedVariables.get(k);
			if (mAssignments.containsKey(xk)) {
				int i = k + 1;
				while (i < mOrderedVariables.size()) {
					final Term xi = mOrderedVariables.get(i);
					if (!mAssignments.containsKey(xi)) {
						break;
					}
					mAssignments.remove(xi);
					i++;
				}
			}
			final Rational updateValue = computeSatisfyingValue(xk);
			mAssignments.put(xk, updateValue);
		}

		/**
		 * Compute a value for a variable such that it satisfies all constraints of its level
		 */
		private Rational computeSatisfyingValue(Term topVar) {
			if (mTopVariables.get(topVar).isEmpty()) {
				return Rational.ZERO;
			}
			// Compute lower and upper bounds
			// TODO Should we store the max lower bound and min upper bound at all times?
			InfinitNumber lowerBound = InfinitNumber.NEGATIVE_INFINITY;
			InfinitNumber upperBound = InfinitNumber.POSITIVE_INFINITY;
			for (Term constraint : mTopVariables.get(topVar)) {
				final InterpolatorAffineTerm constraintLHS = mConstraints.get(constraint);
				final Rational factor = constraintLHS.getSummands().get(topVar);
				final InterpolatorAffineTerm lhsWithoutXk =
						new InterpolatorAffineTerm(constraintLHS).add(factor.negate(), topVar);
				InfinitNumber bound = evaluateTerm(lhsWithoutXk);
				if (factor.isNegative()) {
					if (!bound.lesseq(lowerBound)) {
						lowerBound = bound;
					}
				} else {
					bound = bound.negate();
					if (bound.less(upperBound)) {
						upperBound = bound;
					}
				}
			}
			// Find a Rational in between. It must exist, else a conflict would have been detected.
			final Rational satisfyingValue;
			if (lowerBound.equals(InfinitNumber.NEGATIVE_INFINITY)) {
				satisfyingValue = upperBound.mA.sub(Rational.ONE);
			} else if (upperBound.equals(InfinitNumber.POSITIVE_INFINITY)) {
				satisfyingValue = lowerBound.mA.add(Rational.ONE);
			} else {
				satisfyingValue = upperBound.mA.sub(upperBound.mA.sub(lowerBound.mA).div(Rational.TWO));
			}
			return satisfyingValue;
		}

		/**
		 * Get the constraints, both initial and learned, from the conflict resolution.
		 * 
		 * @return A map of the constraints and their level.
		 */
		private Map<Term, Integer> getConstraints() {
			Map<Term, Integer> constraintsWithLevel = new HashMap<Term, Integer>();
			for (Entry<Term, Set<Term>> topVar : mTopVariables.entrySet()) {
				int level = mOrderedVariables.indexOf(topVar.getKey());
				for (Term constraint : topVar.getValue()) {
					constraintsWithLevel.put(constraint, level);
				}
			}
			return constraintsWithLevel;
		}

		/* Helper methods */

		/**
		 * Get the top variable of a constraint w.r.t. the given order on the variables.
		 */
		private Term computeTopVar(InterpolatorAffineTerm constraintLHS, int maxLevel) {
			for (int k = maxLevel; k >= 0; k--) {
				final Term var = mOrderedVariables.get(k);
				if (constraintLHS.getSummands().containsKey(var)) {
					return var;
				}
			}
			return mOrderedVariables.get(0);
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
				assert mAssignments.containsKey(var);
				final Rational coeff = constraintLHS.getSummands().get(var);
				final Rational value = mAssignments.get(var);
				final Rational mult = coeff.mul(value);
				evaluated = evaluated.addmul(InfinitNumber.ONE, mult);
			}
			evaluated = evaluated.add(constraintLHS.getConstant());
			return evaluated;
		}
	}
}
