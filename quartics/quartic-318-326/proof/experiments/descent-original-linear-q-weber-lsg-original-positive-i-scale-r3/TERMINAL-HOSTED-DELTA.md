# Original positive-I Scale20: exact final-owner diagnostic repair

Exact official Scale20r2 compiled 19/20 sources and passed the strict
558-declaration audit with zero verified baseline and no reuse. Both
previously diagnosed ShortScale and UnitSquarePeriod compiled. Only
OriginalPositiveIScale318 was rejected. The raw source and all predecessor
log evidence are bound in this revision's manifest and reversible delta.

* L48: use the actual pinned `Complex.ofReal_ne_zero` on the literal
  scale coercion (Mathlib Basic/Complex/Basic line 141).
* L69: use private typed nonsingularity transport across the same
  actual model equality; there is no untyped dependent substitution.
* L89: place the nonzero numerical witness literally in the public type
  rather than referring to the inaccessible private proof. Same turn.

There is no import, workflow, declaration-boundary, statement-meaning,
vendor attribution or resource-budget change. The nineteen other sources
are byte-identical. Only source and parser checks have been run here;
the final endpoint has not been claimed.
