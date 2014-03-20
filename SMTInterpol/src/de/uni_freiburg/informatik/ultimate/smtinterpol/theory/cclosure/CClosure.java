/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTermPairHash.Info.Entry;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayQueue;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class CClosure implements ITheory {
	private final class CCAppTermPair {
		final CCAppTerm mFirst, mSecond;
		public CCAppTermPair(CCAppTerm first,CCAppTerm second) {
			this.mFirst = first;
			this.mSecond = second;
		}
		public int hashCode() {
			// Needs to be symmetric
			return mFirst.hashCode() + mSecond.hashCode();
		}
		public boolean equals(Object o) {
			if (o instanceof CCAppTermPair) {
				CCAppTermPair p = (CCAppTermPair)o;
				return (mFirst == p.mFirst && mSecond == p.mSecond) 
					|| (mFirst == p.mSecond && mSecond == p.mFirst);
			}
			return false;
		}
		public String toString() {
			return mFirst + " " + mSecond;
		}
	}
	final DPLLEngine mEngine;
	final ArrayList<CCTerm> mAllTerms = new ArrayList<CCTerm>();
	final CCTermPairHash mPairHash = new CCTermPairHash();
	final ArrayQueue<Literal> mPendingLits = new ArrayQueue<Literal>();
	final ScopedHashMap<Object, CCTerm> mSymbolicTerms =
			new ScopedHashMap<Object, CCTerm>();
	int mNumFunctionPositions;
	int mMergeDepth;
	final ArrayDeque<CCTerm> mMerges = new ArrayDeque<CCTerm>();
	final ArrayDeque<CCAppTermPair> mPendingCongruences =
		new ArrayDeque<CCAppTermPair>();
	
	final Clausifier mClausifier;
	
	private long mInvertEdgeTime, mEqTime, mCcTime, mSetRepTime;
	private long mCcCount, mMergeCount;

	public CClosure(DPLLEngine engine, Clausifier clausifier) {
		this.mEngine = engine;
		this.mClausifier = clausifier;
	}
	
	public CCTerm createAnonTerm(SharedTerm flat) {
		CCTerm term = new CCBaseTerm(false, mNumFunctionPositions, flat, flat);
		mAllTerms.add(term);
		return term;
	}


	public CCTerm createAppTerm(boolean isFunc, CCTerm func, CCTerm arg) {
		assert func.mIsFunc;
		CCParentInfo info = arg.mRepStar.mCCPars.getExistingParentInfo(func.mParentPosition);
		if (info != null) {
			SimpleList<CCAppTerm.Parent> prevParents = info.mCCParents;
			assert prevParents.wellformed();
			for (CCAppTerm.Parent termpar : prevParents) {
				CCAppTerm term = termpar.getData();
				if (term.mFunc == func && term.mArg == arg) {
					return term;
				}
			}
		}
		CCAppTerm term = new CCAppTerm(isFunc, 
				isFunc ? func.mParentPosition + 1 : 0, func, arg, null, this);
		CCAppTerm congruentTerm = term.addParentInfo(this);
		if (congruentTerm != null) {
			// Here, we do not have the resulting term in the equivalence class
			// Mark pending congruence
			addPendingCongruence(term, congruentTerm);
		}
		return term;
	}
	
	private CCTerm convertFuncTerm(FunctionSymbol sym, CCTerm[] args, int numArgs) {
		if (numArgs == 0) {
			CCTerm term = mSymbolicTerms.get(sym);
			if (term == null) {
				term = new CCBaseTerm(
				        args.length > 0, mNumFunctionPositions, sym, null);
				mNumFunctionPositions += args.length;
				mSymbolicTerms.put(sym, term);
			}
			return term;
		} else {
			CCTerm pred = convertFuncTerm(sym, args, numArgs - 1);
			return createAppTerm(numArgs < args.length, pred, args[numArgs - 1]);
		}
	}
	
	/**
	 * Function to retrieve the CCTerm representing a function symbol.
	 * @param sym Function symbol.
	 * @return CCTerm representing this function symbol in the egraph.
	 */
	public CCTerm getFuncTerm(FunctionSymbol sym) {
		CCTerm term = mSymbolicTerms.get(sym);
		if (term == null) {
			term = new CCBaseTerm(sym.getParameterSorts().length > 0,
					mNumFunctionPositions,sym,null);
			mNumFunctionPositions += sym.getParameterSorts().length;
			mSymbolicTerms.put(sym,term);
		}
		return term;
	}
	
	public void insertEqualityEntry(CCTerm t1, CCTerm t2, 
								    CCEquality.Entry eqentry) {
		if (t1.mMergeTime > t2.mMergeTime) {
			CCTerm tmp = t1;
			t1 = t2;
			t2 = tmp;
		}
			
		if (t1.mRep == t1) {
			assert t2.mRep == t2;
			CCTermPairHash.Info info = mPairHash.getInfo(t1, t2);
			if (info == null) {
				info = new CCTermPairHash.Info(t1, t2);
				mPairHash.add(info);
			}
			info.mEqlits.prependIntoJoined(eqentry, true);
		} else {
			boolean isLast = t1.mRep == t2;
			boolean found = false;
			for (CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
//				assert (!info.eqlits.isEmpty());
				if (pentry.mOther == t2) {
					info.mEqlits.prependIntoJoined(eqentry, isLast);
					found = true;
					break;
				}
			}
			if  (!found) {
				CCTermPairHash.Info info = new CCTermPairHash.Info(t1, t2);
				info.mRhsEntry.unlink();
				info.mEqlits.prependIntoJoined(eqentry, isLast);
			}
			if (!isLast)
				insertEqualityEntry(t1.mRep, t2, eqentry);
		}
	}
	
	public CCEquality createCCEquality(int stackLevel, CCTerm t1, CCTerm t2) {
		assert (t1 != t2);
		CCEquality eq = null;
		assert t1.invariant();
		assert t2.invariant();
		
		eq = new CCEquality(stackLevel, t1, t2);
		insertEqualityEntry(t1, t2, eq.getEntry());
		mEngine.addAtom(eq);
		
		assert t1.invariant();
		assert t2.invariant();
		assert t1.pairHashValid(this);
		assert t2.pairHashValid(this);
		
		if (t1.mRepStar == t2.mRepStar) {
			if (mEngine.getLogger().isDebugEnabled())
				mEngine.getLogger().debug("CC-Prop: " + eq + " repStar: " + t1.mRepStar);
			mPendingLits.add(eq);
		} else {
			CCEquality diseq = mPairHash.getInfo(t1.mRepStar, t2.mRepStar).mDiseq; 
			if (diseq != null) {
				if (mEngine.getLogger().isDebugEnabled())
					mEngine.getLogger().debug("CC-Prop: " + eq.negate() + " diseq: " + diseq);
				eq.mDiseqReason = diseq;
				mPendingLits.add(eq.negate());
			}
		}
		return eq;
	}
	public boolean knowsConstant(FunctionSymbol sym) {
		return mSymbolicTerms.containsKey(sym);
	}
	public CCTerm createFuncTerm(
			FunctionSymbol sym, CCTerm[] subterms, SharedTerm fapp) {
		CCTerm term = convertFuncTerm(sym, subterms, subterms.length);
		if (term.mFlatTerm == null) {
			mAllTerms.add(term);
		}
		term.mFlatTerm = fapp;
		return term;
	}
	
	public void addTerm(CCTerm term, SharedTerm shared) {
		term.mFlatTerm = shared;
		mAllTerms.add(term);
	}
			
	@Override
	public void backtrackLiteral(Literal literal) {
		if (!(literal.getAtom() instanceof CCEquality))
			return;
		CCEquality eq = (CCEquality) literal.getAtom();
		if (eq.mStackDepth != -1) {
			backtrackStack(eq.mStackDepth);
			eq.mStackDepth = -1;
			if (literal != eq)
				undoSep(eq);
		}
	}

	@Override
	public Clause computeConflictClause() {
		Clause res = checkpoint();
		if (res == null)
			res = checkpoint();
		assert mPendingCongruences.isEmpty();
		return res;
	}
	
	public Literal getPropagatedLiteral() {
		Literal lit = mPendingLits.poll();
		assert (lit == null || checkPending(lit));
		return lit;
	}
	
	@Override
	public Clause getUnitClause(Literal lit) {
		if (lit.getAtom() instanceof LAEquality) {
			LAEquality laeq = (LAEquality) lit.getAtom();
			for (CCEquality eq : laeq.getDependentEqualities()) {
				if (eq.getStackPosition() >= 0 
					&& eq.getStackPosition() < laeq.getStackPosition() 
					&& eq.getDecideStatus().getSign() == lit.getSign()) {
					return new Clause(new Literal[] { 
					     eq.getDecideStatus().negate(), lit },
							new LeafNode(LeafNode.EQ, null));
				}
			}
			throw new AssertionError("Cannot find explanation for " + laeq);
		} else if (lit instanceof CCEquality) {
			CCEquality eq = (CCEquality) lit;
			return computeCycle(eq);
		} else {
			/* ComputeAntiCycle */
			CCEquality eq = (CCEquality) lit.negate();
			return computeAntiCycle(eq);
		}
	}

	@Override
	public Clause setLiteral(Literal literal) {
		if (!(literal.getAtom() instanceof CCEquality))
			return null;
		CCEquality eq = (CCEquality) literal.getAtom();
		LAEquality laeq = eq.getLASharedData(); 
		if (laeq != null) {
			assert ((List<CCEquality>)laeq.getDependentEqualities()).contains(eq);
			if (laeq.getDecideStatus() != null
				&& laeq.getDecideStatus().getSign() != literal.getSign()) {
				return new Clause(new Literal[] { 
					laeq.getDecideStatus().negate(), literal.negate() },
						new LeafNode(LeafNode.EQ, null));
			}
			mPendingLits.add(literal == eq ? laeq : laeq.negate());
		}
		if (literal == eq) {
			if (eq.getLhs().mRepStar != eq.getRhs().mRepStar) {
				eq.mStackDepth = mMerges.size();
				Clause conflict = eq.getLhs().merge(this, eq.getRhs(), eq);
				if (conflict != null)
					return conflict;
			}
		} else {
			CCTerm left = eq.getLhs().mRepStar;
			CCTerm right = eq.getRhs().mRepStar;
			
			/* Check for conflict */
			if (left == right) {
				Clause conflict = computeCycle(eq);
				if (conflict != null)
					return conflict;
			}
			/* TODO get array extensionality working! */
			/*if (eq.isArray()) {
				// This is ext-diseq
				Info info = pairHash.getInfo(left, right);
				info.addExtensionalityDiseq(converter);
			}*/
			separate(left, right, eq);
			eq.mStackDepth = mMerges.size();
		}
		return null;
	}

	private CCTermPairHash.Info mLastInfo;
	private void separate(CCTerm lhs, CCTerm rhs, CCEquality atom) {
		if (mLastInfo == null || !mLastInfo.equals(lhs, rhs)) {
			mLastInfo = mPairHash.getInfo(lhs, rhs);
			assert mLastInfo != null;
		}
		if (mLastInfo.mDiseq != null)
			return;

		mLastInfo.mDiseq = atom;
		/* Propagate inequalities */
		for (CCEquality.Entry eqentry : mLastInfo.mEqlits) {
			CCEquality eq = eqentry.getCCEquality();
			if (eq.getDecideStatus() == null) {
				eq.mDiseqReason = atom;
				addPending(eq.negate());
			}
		}
		/* reverse congruence closure
		for (CCTerm t1 : members) {
			if (t1 instanceof CCAppTerm) {
				CCAppTerm app1 = (CCAppTerm) t1;
				for (CCTerm t2 : members) {
					if (t2 instanceof CCAppTerm) {
						CCAppTerm app2 = (CCAppTerm) t2;
						if (app1.func.rep == app2.func.rep
							&& !app1.arg.rep.inDiseq(app2.arg.rep.diseq)) {
							separate(app1.arg.rep, app2.arg.rep, atom);
						} else if (app1.arg.rep == app2.arg.rep
								   && !app1.func.rep.inDiseq(app2.func.rep.diseq)) {
							separate(app1.func.rep, app2.func.rep, atom);
						}
					}
				}
			}
		} */
	}
	
	private void undoSep(CCEquality atom) {
		atom.mDiseqReason = null;
		CCTermPairHash.Info destInfo = mPairHash.getInfo(
				atom.getLhs().mRepStar, atom.getRhs().mRepStar);
		if (destInfo != null && destInfo.mDiseq != null) {
			destInfo = mPairHash.getInfo(
					atom.getLhs().mRepStar, atom.getRhs().mRepStar);
			if (destInfo.mDiseq == atom)
				destInfo.mDiseq = null;
		}
	}	

	public Clause computeCycle(CCEquality eq) {
		CongruencePath congPath = 
			new CongruencePath(this);
		Clause res = congPath.computeCycle(eq, mEngine.isProofGenerationEnabled());
		assert(res.getSize() != 2 || res.getLiteral(0).negate() != res.getLiteral(1));
		return res;
	}
	public Clause computeCycle(CCTerm lconstant,CCTerm rconstant) {
		CongruencePath congPath = 
			new CongruencePath(this);
		return congPath.computeCycle(lconstant,rconstant, mEngine.isProofGenerationEnabled());
	}
		
	public Clause computeAntiCycle(CCEquality eq) {
		CCTerm left = eq.getLhs();
		CCTerm right = eq.getRhs();
		CCEquality diseq = eq.mDiseqReason;
		assert left.mRepStar != right.mRepStar;
		assert diseq.getLhs().mRepStar == left.mRepStar
			|| diseq.getLhs().mRepStar == right.mRepStar;
		assert diseq.getRhs().mRepStar == left.mRepStar
			|| diseq.getRhs().mRepStar == right.mRepStar;

		left.invertEqualEdges(this);
		left.mEqualEdge = right;
		left.mOldRep = left.mRepStar;
		assert left.mOldRep.mReasonLiteral == null;
		left.mOldRep.mReasonLiteral = eq;
		Clause c = computeCycle(diseq);
		assert left.mEqualEdge == right && left.mOldRep == left.mRepStar;
		left.mOldRep.mReasonLiteral = null;
		left.mOldRep = null;
		left.mEqualEdge = null;
		return c;
	}
	
	public void addPending(Literal eq) {
		assert checkPending(eq);
		mPendingLits.add(eq);
	}

	private boolean checkPending(Literal literal) {
		if (literal.negate() instanceof CCEquality) {
			CCEquality eq = (CCEquality) literal.negate();
			CCTerm left = eq.getLhs();
			CCTerm right = eq.getRhs();
			CCEquality diseq = eq.mDiseqReason;
			assert left.mRepStar != right.mRepStar;
			assert diseq.getLhs().mRepStar == left.mRepStar
				|| diseq.getLhs().mRepStar == right.mRepStar;
			assert diseq.getRhs().mRepStar == left.mRepStar
				|| diseq.getRhs().mRepStar == right.mRepStar;
			return true;
		}
		if (literal instanceof CCEquality) {
			CCEquality eq = (CCEquality)literal;
			return (eq.getLhs().mRepStar == eq.getRhs().mRepStar);
		}
		if (literal.getAtom() instanceof LAEquality) {
			LAEquality laeq = (LAEquality) literal.getAtom();
			for (CCEquality eq : laeq.getDependentEqualities()) {
				if (eq.getDecideStatus() != null
						&& eq.getDecideStatus().getSign() == literal.getSign())
					return true;
			}
		}
		return false;
	}

	public Clause checkpoint() {
		// TODO Move some functionality from setLiteral here.
		while (!mPendingCongruences.isEmpty()/* || root.next != root*/) {
			Clause res = buildCongruence(true);
			return res;// NOPMD
		}
		return null;
	}
	
	public Term convertTermToSMT(CCTerm t) {
		return t.toSMTTerm(mEngine.getSMTTheory());
	}

	public Term convertEqualityToSMT(CCTerm t1, CCTerm t2) {
		return mEngine.getSMTTheory().equals(convertTermToSMT(t1), 
				convertTermToSMT(t2));
	}
	

	public void dumpModel(LogProxy logger) {
//		assert(checkCongruence());
		logger.info("Equivalence Classes:");
		for (CCTerm t : mAllTerms) {
			if (t == t.mRepStar) {
				StringBuilder sb = new StringBuilder();
				String comma = "";
				for (CCTerm t2 : t.mMembers) {
					sb.append(comma).append(t2);
					comma = "=";
				}
				logger.info(sb.toString());
			}
		}
	}

	@SuppressWarnings("unused")
	private boolean checkCongruence() {
		boolean skip;
		for (CCTerm t1 : mAllTerms) {
			skip = true;
			for (CCTerm t2 : mAllTerms) {
				if (skip) {
					if (t1 == t2)
						skip = false;
					continue;
				}
				if (t1 instanceof CCAppTerm && t2 instanceof CCAppTerm) {
					CCAppTerm a1 = (CCAppTerm)t1;
					CCAppTerm a2 = (CCAppTerm)t2;
					if (a1.mFunc.mRepStar == a2.mFunc.mRepStar
							&& a1.mArg.mRepStar == a2.mArg.mRepStar
							&& a1.mRepStar != a2.mRepStar) {
						System.err.println("Should be congruent: " + t1 + " and " + t2);
						return false;
					}
				}
			}
		}
		return true;
	}
	
	public void printStatistics(LogProxy logger) {
		logger.info("CCTimes: iE " + mInvertEdgeTime + " eq "
				+ mEqTime + " cc " + mCcTime + " setRep "
				+ mSetRepTime);
		logger.info("Merges: " + mMergeCount + ", cc:" + mCcCount);
	}

	@Override
	public Literal getSuggestion() {
		// CClosure does not need to suggest anything so far!
		return null;
	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public Clause backtrackComplete() {
		mPendingLits.clear();
		return buildCongruence(true);
	}

	@Override
	public void restart(int iteration) {
		// Nothing to do
	}

	@Override
	public Clause startCheck() { return null; }
	
	@Override
	public void endCheck() {
		// Nothing to do
	}
	
	void addPendingCongruence(CCAppTerm first,CCAppTerm second) {
		assert(first.mLeftParInfo.inList() && second.mLeftParInfo.inList());
		assert(first.mRightParInfo.inList() && second.mRightParInfo.inList());
		mPendingCongruences.add(new CCAppTermPair(first,second));
	}
	
	void prependPendingCongruence(CCAppTerm first,CCAppTerm second) {
		assert(first.mLeftParInfo.inList() && second.mLeftParInfo.inList());
		assert(first.mRightParInfo.inList() && second.mRightParInfo.inList());
		mPendingCongruences.addFirst(new CCAppTermPair(first,second));
	}
	
	private Clause buildCongruence(boolean checked) {
		CCAppTermPair cong;
		while ((cong = mPendingCongruences.poll()) != null) {
			mEngine.getLogger().debug(new DebugMessage("PC {0}", cong));
			Clause res = null;
			// TODO Uncomment checked here
			if (/*!checked ||*/ 
					(cong.mFirst.mArg.mRepStar == cong.mSecond.mArg.mRepStar
						&& cong.mFirst.mFunc.mRepStar == cong.mSecond.mFunc.mRepStar)) {
				res = cong.mFirst.merge(this,cong.mSecond,null);
			} else
				assert checked : "Unchecked buildCongruence with non-holding congruence!";
			if (res != null) {
				return res;
			}
		}
		return null;
	}	

	private void backtrackStack(int todepth) {
		while (mMerges.size() > todepth) {
			CCTerm top = mMerges.pop();
			top.mRepStar.invertEqualEdges(this);
			boolean isCongruence = top.mOldRep.mReasonLiteral == null;
			CCTerm lhs = top;
			CCTerm rhs = top.mEqualEdge;
			top.undoMerge(this, top.mEqualEdge);
			if (isCongruence) {
				assert (rhs instanceof CCAppTerm);
				prependPendingCongruence((CCAppTerm)lhs, (CCAppTerm)rhs);
			}
		}
	}

	public int getStackDepth() {
		return mMerges.size();
	}
	
	@Override
	public void removeAtom(DPLLAtom atom) {
		if (atom instanceof CCEquality) {
			CCEquality cceq = (CCEquality) atom;
			removeCCEquality(cceq.getLhs(), cceq.getRhs(), cceq);
		}
	}
	private void removeCCEquality(CCTerm t1, CCTerm t2, CCEquality eq) {
		// TODO Need test for this!!!
		if (t1.mMergeTime > t2.mMergeTime) {
			CCTerm tmp = t1;
			t1 = t2;
			t2 = tmp;
		}
			
		if (t1.mRep == t1) {
			assert t2.mRep == t2;
			CCTermPairHash.Info info = mPairHash.getInfo(t1, t2);
			if (info == null) {
				// We never created a pair hash for this...
				return;
			}
			info.mEqlits.prepareRemove(eq.getEntry());
			eq.getEntry().removeFromList();
			if (info.isEmpty()) {
				mPairHash.removePairInfo(info);
			}
		} else {
			boolean isLast = t1.mRep == t2;
			boolean found = false;
			for (CCTermPairHash.Info.Entry pentry : t1.mPairInfos) {
				CCTermPairHash.Info info = pentry.getInfo();
				if (pentry.mOther == t2) {
					info.mEqlits.prepareRemove(eq.getEntry());
					found = true;
					break;
				}
			}
			assert found;
			if (isLast)
				eq.getEntry().removeFromList();
			else
				removeCCEquality(t1.mRep, t2, eq);
		}
		if (eq.getLASharedData() != null)
			eq.getLASharedData().removeDependentAtom(eq);
	}

	private void removeTerm(CCTerm t) {
		assert t.mRepStar == t;
		assert mPendingCongruences.isEmpty();
		for (Entry e : t.mPairInfos)
			mPairHash.removePairInfo(e.getInfo());
		if (t.mSharedTerm != null)
			t.mSharedTerm = null;
	}
	
	@Override
	public void pop(Object object, int targetlevel) {
		StackData sd = (StackData) object;
		for (int i = mAllTerms.size() - 1; i >= sd.mAllTermsSize; --i) {
			CCTerm t = mAllTerms.get(i);
			removeTerm(t);
			mAllTerms.remove(i);
		}
		mNumFunctionPositions = sd.mNumFuncPositions;
		mSymbolicTerms.endScope();
	}

	@Override
	public Object push() {
		mSymbolicTerms.beginScope();
		return new StackData(this);
	}

	@Override
	public Object[] getStatistics() {
		return new Object[]{
			":CC", new Object[][]{
				{"Merges", mMergeCount},
				{"Closure", mCcCount},
				{"Times", new Object[][]{
					{"Invert", mInvertEdgeTime},
					{"Eq", mEqTime},
					{"Closure", mCcTime},
					{"SetRep", mSetRepTime}}
				}
			}};
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		CCTerm trueNode = null, falseNode = null;
		if (!mAllTerms.isEmpty()) {
			CCTerm t0 = mAllTerms.get(0);
			SharedTerm shared0 = t0.getFlatTerm();
			if (shared0.getTerm() == t.mTrue) {
				trueNode = t0;
				falseNode = mAllTerms.get(1);
			} else if (shared0.getTerm() == t.mFalse) {
				falseNode = t0;
				trueNode = mAllTerms.get(1);
			}
		}
		new ModelBuilder(mAllTerms, model, t, ste, trueNode, falseNode);
	}
	
	void addInvertEdgeTime(long time) {
		mInvertEdgeTime += time;
	}
	
	void addEqTime(long time) {
		mEqTime += time;
	}
	
	void addCcTime(long time) {
		mCcTime += time;
	}
	
	void addSetRepTime(long time) {
		mSetRepTime += time;
	}

	void incCcCount() {
		++mCcCount;
	}
	
	void incMergeCount() {
		++mMergeCount;
	}
	
}
