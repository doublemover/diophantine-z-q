# Independent review of tame formal-coordinate linearization

Accepted at its explicitly equal-characteristic, constant-zero scope. The two copied modules and exhaustive audit were freshly rebuilt with strict kernel checking: 51 declarations passed, with standard axioms only. Exact source equality with the frozen author packet was verified.

## Checks

- `sigma F` really is the substitution map P -> P(F), and `orbit j` is its j-th iterate on X. The successor recurrence therefore has the correct composition orientation. Constant coefficient zero is used wherever formal substitution requires it.
- The formal chain rule gives the actual coefficient-one multiplication formula. It is not an assumed tangent representation. Iterating it gives the actual tangent power lambda^j and hence lambda^n=1 from the period.
- The unweighted average includes exactly j=0,...,n-1. Shifting the orbit sum has equal boundary terms because the nth orbit equals X. The coefficient of X is one precisely after division by the nonzero cast of n. This hypothesis excludes n=0 and characteristic dividing n.
- The invariant parameter H has actual constant coefficient zero and unit linear coefficient. The actual compositional inverse is used with the correct orientation to turn H(F)=H into F=X. No cancellation of an unproved injective substitution is assumed.
- The weighted average uses lambda^(-j), giving sigma(weightedOrbit j)=lambda*weightedOrbit(j+1). The period lambda^n=1 makes its boundary term agree. Thus H(F)=lambda H is the correct character and not its inverse.
- In `conjugated_linear`, the nested substitution is H(F(H^{-1}(X)))=lambda X. The inverse-substitution identity is on the correct side. Both constant-zero and unit-tangent hypotheses for the formal inverse are supplied by the constructed parameter.
- The existence theorem derives lambda nonzero from lambda^n=1 and n nonzero. A separate nonzero-tangent hypothesis is not silently retained. Characteristic zero is used only in its dedicated positive-period specialization; general tame characteristic is allowed.

## Remaining geometry and exclusions

This is a theorem about actual k[[X]] over a field. Identifying a smooth curve's completed local ring with k[[X]], expressing the actual continuous action as substitution, and proving the relevant finite stabilizer order is invertible remain geometric inputs. No mixed-characteristic shifted-constant chart is proved. The averaging proof cannot be applied when the period vanishes in the residue characteristic, and the API correctly excludes that case.

No quotient curve, branch model, integral stack or whole five-contact result is asserted. The actual finite-order formal-coordinate algebra is fully checked within the stated scope.

## Replay

Run `bash tame-coordinate-review/run.sh`. The receipt and hashes bind copied sources, producer note, logs, audit and original frozen receipt. No original source or repository file was changed.
