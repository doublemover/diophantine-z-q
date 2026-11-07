# Final low/high polynomial congruence transfer

The two modules close the bounded polynomial and numerator-divisibility steps after the source/local logarithm congruences.

- `LucasCongruence318.lucas_congruent` proves integral valuation congruence preservation for the exact literal quartic b^2-a*(a-2)*b*c+(a-2)^2*c^2-1, with generic field and additive valuation.
- `LucasCongruence318.integer_lucas_dvd` takes integral p-adic a,b,c, depth13 congruences to integer labels A,B,C, and depth13 of the literal source quartic. It concludes p^13 divides B^2-A*(A-2)*B*C+(A-2)^2*C^2-1.
- `BetaCongruence318.beta_depth` transfers L-beta and L-N depth4 to beta-N depth4. The intermediary L need not be integral.
- `BetaCongruence318.beta_numerator_dvd` concludes p^4 divides the reduced rational numerator of beta-N.
- `rational_numerator_dvd` proves the general numerator-divisibility step, including zero, by multiplying by the actual integral rational denominator. No denominator-unit assumption is required.

The only retained inputs are the explicit finite valuation congruences and integrality stated in the theorem. Producing them from the literal source and coherent global labels is the separate source-label packet; this module does not replace that production with an abstract arithmetic predicate.

Fresh strict kernel replay: bash run.sh. Full recursive audit passes 18 declarations in two modules with only propext, Classical.choice, Quot.sound. Source/dependency hashes are recorded in the receipt. No Git/repository edits are made here.
