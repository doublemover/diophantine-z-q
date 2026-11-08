# Normality of the entire rational completed-curve charts

`CompletedRationalNormal318.affine` and `.infinity` prove that both actual rings `ShortAffineJacobian318.Ring A B` and `InfinityChart318.Ring A B` are integrally closed for every A,B in Q with unit discriminant. These are the full affine chart rings, not just chosen Jacobian localizations. There is no B nonzero condition, extra model identification, or supplied normality premise.

The proof first establishes `EtaleDomainNormal318.integrallyClosed`: an etale domain over a normal domain is normal. Only the actual generic fiber is required to be finite; its finiteness follows from formal unramifiedness over the fraction field. Smooth integral-closure base change proves the algebra integrally closed in this actual generic field.

`SmoothDomainNormal318.integrallyClosed` then proves that a smooth domain over any field is normal. Actual principal neighborhoods are standard etale over polynomial rings, which are normal; these neighborhoods cover by their explicitly chosen prime-avoiding denominators. Principal-open normality descent closes the whole ring. The concrete final module supplies the previously proved actual domain and smoothness of each chart.

Three sources passed bounded strict checks and the recursive audit. This author packet does not itself prove the separate canonical normalization comparison an isomorphism; that consumer must still use these exact chart rings and its actual integral/birational comparison. It also does not supply PEL, polarized Jacobian, Hodge/metric or final arithmetic identifications. No whole-chain replay or independent self-acceptance is claimed.
