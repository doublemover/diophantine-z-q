# Actual finite-field inputs for the simultaneous-prime sieve

## Historical source and scope

Read the actual local-count lemma and proof in quartics/quartic-318-326/docs/sources/quartic_v10.tex lines16547–16590, within the simultaneous-prime theorem's appendix. Its first claim is that a²+b²−c²−d²−κw²=0 has q⁴−1 nonzero solutions when characteristic is odd and κ is nonzero. The proof begins with the two literal Gaussian norm-fiber counts. This successor formalizes those counts and the complete quadric count, in both split and inert cases. It does not assert the later primitive integral asymptotic, sieve tail, fixed-field prime/Artin estimate, transference or final simultaneous prime existence.

All239 sources of the independently source-reviewed Jacobi CM producer are byte-identical. Four new modules implement actual coordinate equivalences and finite cardinalities; their output is not a density assumption.

## Difference conic and character sum

For nonzero t, the literal hyperbola xy=t is explicitly equivalent to Fˣ by projection to x, with inverse x↦(x,t/x). The literal difference conic x²−y²=t is equivalent to it through(x−y,x+y), with inverse((u+v)/2,(v−u)/2). Characteristic-two exclusion is retained through nonzero2.

The same conic is equivalent to the disjoint family of all ordinate fibers y²=x²−t. The actual square-root count, including zero, then gives sum_x chi(x²−t)=−1. Cardinality of Fˣ is q−1; the natural-to-integer subtraction uses q>1 explicitly.

## Norm fibers in both splitting cases

NormFiber(t) is the literal pair subtype x²+y²=t. Its full ordinate-fiber decomposition gives #NormFiber(t)=q+sum_x chi(t−x²). Factoring−1 and applying the difference-conic calculation gives q−chi(−1) for every nonzero t.

For t=0, the sum of chi(x²) is q−1: erase exactly x=0 and use chi(x²)=1 at every other element. Hence #NormFiber(0)=q+(q−1)chi(−1). No assumption that−1 is square or nonsquare is necessary, so both cases are covered by the same actual formula.

## Pairs of norm fibers

The actual four-coordinate difference n(a,b)−n(c,d)=s is equivalent to the family over t of NormFiber(t)×NormFiber(t−s). Write A=q−epsilon and B=q epsilon, epsilon=chi(−1), so each fiber count is A+B times the zero indicator. Multiplying and summing the two indicators produces qA²+2AB plus B² exactly when s=0. Since epsilon²=1, the resulting count is

q³−q + (q² if s=0, else0).

The exceptional zero difference is indispensable and is not discarded.

## Original five coordinates and nonzero vectors

Quadric(κ) retains the literal five coordinates(a,b,c,d,w). It is explicitly equivalent to the family over w of NormDifference(κw²). Since κ is nonzero, κw²=0 iff w=0. The exceptional q² contribution occurs once, cancelling the−q² from the q generic fibers and giving exactly q⁴ points. Removing precisely the literal origin gives q⁴−1 nonzero points.

Thus the local-density denominator used by the original analytic theorem is constructed on the correct source and with the correct primitive/nonzero condition. This does not yet count the forbidden adjacent-norm loci or prove the analytic asymptotic.

## Validation boundary

Finite checks cover279 norm fibers,279 norm-difference fibers,266 nonzero-κ quadrics, and17,068 literal five-coordinate points. Zeroκ and characteristic2 are genuine negative controls. Static dependency/placeholder/hash checks and audit-history self-test are separate from hosted Lean and independent source review. No local Lean was run.
