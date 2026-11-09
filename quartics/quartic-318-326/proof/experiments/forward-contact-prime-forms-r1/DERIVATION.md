# Exact contact forms, merging, and the same-index source

## Historical comparison and primary producers

Read the actual COMPLETENESS-ASSEMBLY.md sections3,6,7 and PRIME-PATTERN-AUDIT.md, not only their verdicts. Historical justification is present: the original proof fixes A0=1,A1=(C0+nC)^2,A2=nC^2, then merges repeated rational contact forms and clears denominators with a square before the simultaneous prime theorem. The current five modules implement that source-specific finite bridge and attach it to the previously implemented all-support scalar/full-source route. This is not a newly discovered mathematical gap and does not formalize the analytic prime-existence proof.

Primary code read: FixedDetectorScales318, ContactWeightWitness318.contact, ThreeDetectorUniformFamily318.contactParameter/witness_squareclass, ScaledDetectorChain318.squareFactor, AllPrimePreparedFullSource318.current_source and the literal source190/241/292 consumers. These preserve actual emitted root signs and the original scale normalization, including c^5 in the scaled trace quotient.

## 1. Original positions and exact square scales

ContactPrimeForms318.root is the literal ordered list 0,-1/2,-1,1/2399,-32/407. Its five entries are distinct. scaleRoot is1,C0+nC,nC for the original fixed label product. Existing fixed-root bounds prove both latter values nonzero; their signs are unrestricted. The actual contactParameter in each row equals scaleRoot^2*t.

Each of fifteen positions (j,k) has slope=-root(k)/scaleRoot(j)^2. Within each row, slopes are injective because its scale is nonzero and the five roots are distinct. Cross-row coincidences are possible and are retained until merging. No independence of all fifteen forms is assumed.

## 2. Constructed denominator and exact merging

For any finite rational family a_i, D=product den(a_i)>0. Each den(a_i) divides D, say D=den(a_i)*k_i. The integer num(a_i)*k_i*D has rational value a_i*D^2. Clearing.construct specializes this to all fifteen original slopes. It is selected after labels, with no dependence on later h,u,w.

The merged set is the image of all fifteen integer coefficients. Every original position belongs to it. Equality of integer coefficients is equivalent to equality of original rational slopes, since D^2 is nonzero. Thus merging is exact and neither drops a distinct form nor invents a new one. The five coefficients in any one original row remain injective. The polynomial value is the actual integer u+c*w^2, and distinct coefficients give distinct values whenever w is nonzero.

## 3. Literal source squareclass and normalization

Set z=D*w and t=u/z^2. For each original c=scaleRoot(j),

F(c^2*t)=product_k(u-root(k)*z^2/c^2)*(c/z)^10.

The constructed coefficient identity identifies every factor with the integer value u+coefficient(j,k)*w^2. The tenth power is the square of(c/z)^5. Combining with the existing actual witness_squareclass gives

pre(190+51*j)=rowProduct(j)*((c/z)^5*originalSquareFactor(j))^2.

This keeps the literal quotient/chain at the exact same h. At j=1,2, originalSquareFactor already includes the prescribed c^5 denominator from ScaledDetectorChain; no extra scale is silently removed. The displayed new square factor is nonzero when the actual pole is positive, as supplied by the original uniform real construction. The valuation theorem holds at EVERY additive valuation, including denominator primes and2. It does not pretend that the square factor is a unit. Negative scale roots and negative w are covered.

## 4. Prime-value output and coverage

Values C u w records w nonzero and positivity/primality of every value at a coefficient in the merged set. It is an explicit required output of the analytic theorem, not an existence claim. Pi is the product of their natural absolute values, hence positive. Each of the fifteen original position-primes divides this one Pi. Every row keeps its five distinct positive prime values and its actual nonzero rational square factor. Duplicate contacts shared by different rows refer to the same selected prime, rather than being counted as separate analytic positions.

No conclusion here asserts the denominator of the pole is square merely from its integer-product squareclass. At a selected prime the rational square factor could have negative valuation; the actual contact-depth/trace-unit argument is still needed to prove v_p(B)=1 there. Gaussian rays, reduction orders and selected-prime separation are also not consequences of Values.

## 5. Same-h full-source consumer and choice order

ContactPrimeFullSource318.current_source consumes the exact all-support predecessor. The original center/label construction fixes J first, then every later positive free d gives the original labels with multiplier3^(2^16)*J*d. Clearing is fixed from those labels. The predecessor then chooses h0,L and all local thresholds before the contact parameter. Its eventually-atTop conclusion supplies a rational lower threshold; a later integer pair u,w satisfying Values and that threshold is admissible.

Pi is now the actual merged product, not an unrelated caller-supplied number. Keep the original positive Mminus/Mplus, gcd(Mminus,L)=16 and all five coprimalities explicit. Specialize the primary exponent to3. The same selected h satisfies primary residue0, opposite residue1 and local residueh0, original scalar bound, fixed root signs, all scalar support-prime preparations, three pole intervals, and all three newly proved prime-product squareclasses. Four Realization inputs are still required at exactly pre190,pre241,pre292 and scalarB at that same h,t. The conclusion remains the current literal CircuitReplay.HasSolution(stage0(Current318FinalPolynomial.scale))(a), not an altered system or prefix.

## Validation and remaining scope

The exact rational checker covers three scale families (including duplicate rows and negative rational scales), signed w, all fifteen coefficient identities and equality equivalences, five-distinct rows, and literal tenth/fifth-power square factors. SymPy verifies the generic contact identity exactly. The checker also binds all four actual realization targets, source indices, Pi^3 and choice order in the final consumer. All161 predecessor source bytes are unchanged; the five new sources have finite1M budgets. Static closure is166/190. No local Lean compilation and no author-written independent acceptance. Hosted elaboration/kernel checking is required. Prime existence/rays/orders, actual contact-depth realization, four rational two-twist Realizations and the global rational-anchor principle remain open formal inputs.
