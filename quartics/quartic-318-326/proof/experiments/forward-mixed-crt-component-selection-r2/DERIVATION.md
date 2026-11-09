# Revision 2: explicit decidable-equality coherence

Hosted run [42573367792](https://github.com/doublemover/diophantine-z-q/actions/runs/42573367792) at commit 272c0fc passed the first 13 prefix predecessors, then exposed the remaining decidable-equality implementation mismatch at the typed reciprocal V-addition comparison. Exact failed source, log and result remain under `../forward-cyclic-prefix-progressions-r2/hosted-failure-42573367792`.

This superset revision adds a private generic lemma proving that affine point addition is independent of the two DecidableEq implementations: their equality follows from Subsingleton.elim, and substitution gives equality of additions. The final typed comparison composes with this proved equality before using the reciprocal addition theorem. It does not rely on naming an internal instance or assuming two implementations are definitionally equal. Original point/chart definitions, all public theorem statements, arithmetic hypotheses and root signs are unchanged. The other 31 Lean sources are unchanged from the preceding mixed-CRT draft.

The narrow repair and the new CRT consumers still await hosted checking. No local Lean compilation or downstream success is claimed.

# Exact mixed CRT and component selection

This isolated packet joins the repository's original prime-pattern CRT equations to component recurrence, then consumes the chosen h in the original coherent source-prefix witness. It does not construct the prime pattern, the concrete component-return modulus, or a good region inside the identity component. Hosted compilation of the two new modules and the prerequisite closure is pending. No local Lean compilation is run.

## Core join

`MixedCRTComponentSelection318.primary_depth_in_component_region` calls the existing `PrimeCRTAssembly.compatible_primary_depth` with unchanged hypotheses. This constructs r satisfying exactly:

- h = 0 modulo Pi^e Mminus;
- h = 1 modulo Mplus;
- h = h0 modulo L.

The common positive step is k = Pi^e Mminus Mplus L. Every r + k t retains all three residues. If m a belongs to G^0, m divides L, and m divides h0, then the L-congruence also gives m divides r. Thus both r a and k a belong to G^0. The now hosted-checked `MonotheticComponentSteps318` supplies closure(Z k a) = G^0 and positive-tail recurrence. Every ambient open set meeting G^0 is reached by the exact same progression beyond any given bound. No multiplication-surjectivity premise on G^0 remains.

The `primary_depth_source64` wrapper preserves the source's full 64m divisibility. If m(2a) belongs to G^0, then 64m a = 32(m(2a)) belongs to G^0. This is an explicit equality in the same group. It does not identify the component quotient of an unrelated elliptic group with the coherent chart group.

## Actual original-source consumer

`ActualMixedCRTPrefix318` specializes to the genuine cyclic closure of the original two-real-embedding coherent orbit, with generator `ActualCyclicClosure318.generatorInClosure`. Its open target region is defined using:

- the exact original scalar threshold |Norm(u_H)| > 1/(100 sqrt(7));
- four absolute rational half-trace guard bounds epsilon_j > 0;
- the original ambient topology restricted to the cyclic closure.

The margins and target-region existence are inputs preceding prime/CRT data. The region must meet the identity component of this exact cyclic closure. This is stronger information than a nonempty region in the full product or full cyclic closure and remains unproved here.

The conclusion constructs one natural h with all three original residues, h > B, original H = [h]P nonzero, the scalar norm bound, four quantitative guard bounds, preservation of arbitrary rational input q, the literal first 51 source rows, and the same four historical fixed signed roots. The actual orbit comparison identifies its scalar/guard values at h with the exact original assignment. The h-1 translation is retained by the original chart definitions. No replacement by zero or one modulo the combined modulus occurs.

## Still-open constructions

The concrete original coherent orbit has not yet been shown to admit a fixed positive m with m(2a) in G^0. A finite-component/actual return-modulus construction is still required. An arbitrary compact monothetic group need not have such a return, so compactness and density alone are not offered as a proof.

The nonempty scalar/guard-good intersection with G^0 is still required. The P-centered good region from the earlier packet is not silently substituted: P has not been placed in G^0. Inherited pole avoidance is not supplied here. The actual prime-pattern theorem and local scalar preparation must still produce the displayed arithmetic inputs. The remaining 237 source rows, opposite-direction height obligations, and full 318/326 arithmetic theorem remain open.

## Provenance and changed application

Historical sources read: `quartics/quartic-318-326/docs/arithmetic.md`, the real-guard/scalar/component/CRT argument at lines 821–1033, and `docs/sources/quartic_v10.tex`, the real-progression lemma at lines 10632–10694. Historical disposition is prior justification found. Current formal disposition is a partial original-input joining theorem, pending hosted checking and distinct review.

The unchanged component-step module passed its standalone hosted check and seven-declaration recursive audit; the integration receipt records the exact run. The coherent V-addition dependency is the version-2 typed-comparison repair, not the failed version-1 rewrite. All other predecessor copies are byte-bound by SOURCE-COPIES.json. The older failure remains preserved in its original packet. No successful check of that pending repair or its downstream consumers is inferred from a dependency-policy check.

No browser tabs were opened.
