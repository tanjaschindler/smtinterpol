package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;

public class EprGroundPredicateAtom extends EprPredicateAtom {

	public EprGroundPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel, pred);
		assert term.getFreeVars().length == 0 : "trying to create a ground atom from a non-ground term";
	}

}
