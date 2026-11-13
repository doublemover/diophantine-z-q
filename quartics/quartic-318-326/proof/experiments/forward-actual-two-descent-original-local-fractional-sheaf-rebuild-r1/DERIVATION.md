# Exact local fractional sheaves of the original ideal

## 1. Actual original global object

Required: The pullback must start from the existing originalRootIdealSheaf, not a new line selected from valuation data.

Constructed and justification: Both actual affine and infinity local-spectrum morphisms compose the old literal chart map. The native pullbackComp inverse and old restrictFunctorIsoPullback inverse lead to the exact old whole-chart restriction/frame.

## 2. Native tensor normalization

Required: Pulling back a tilde ideal must use the actual localization tensor map with its original coefficient value.

Constructed and justification: Uses existing TildePullback318.pullbackIso followed by the old idealExtensionEquiv. Explicit hom_formula and one_tensor record its exact native map and image of every ideal element.

## 3. All affine primes

Required: The affine local pullback should cover arbitrary primes without pretending localization at a point is an open immersion.

Constructed and justification: OriginalAffineAtPrimePullback quantifies all prime ideals and only uses an open immersion for the original affine chart. The point-localization map is treated as an arbitrary Scheme morphism; its native scalar extension is produced by IsLocalization.

## 4. Exact root ideal

Required: At Ta the actual extended ideal must be the original principal maximal ideal.

Constructed and justification: Native Localization.AtPrime.map_eq_maximalIdeal followed by the old actual_root_maximal_principal proves extendedIdeal=span(rootLocalY). n≠0 remains explicit, and y nonzero is supplied by the existing actual local coordinate producer.

## 5. Same original field

Required: The fractional lattices must sit inside the actual original scheme generic field with specific embeddings.

Constructed and justification: rootEmbedding and infinityEmbedding are the canonical actual stalk algebraMap composed with inverse rootEquiv/infinityEquiv. Injectivity, exact named root and exact infinity parameter identity are proved, not assumed.

## 6. Full fractional image and value

Required: An abstract rank-one equivalence is insufficient: its entire image and actual value must be fixed.

Constructed and justification: The generic lattice is the full range of r↦algebraMap(r)*g. Its frame is proved bijective using the actual embedding injectivity and g nonzero. At Ta the principal ideal frame followed by this range frame sends every x to exactly rootEmbedding(x); mem_lattice quantifies all coefficients.

## 7. Infinity sign and old frame

Required: The infinity sheaf must use the actual old projection frame with inverse-u coefficient, not u or an unspecified scalar.

Constructed and justification: Pulls originalInfinityFrame to the actual origin local spectrum and uses the canonical native pullbackUnitIso. The following literal tildeSelf inverse and moduleFrame give the full range b/u; module_value records the exact inverse sign in the original function field.

## 8. Native sheaf consumers

Required: The local sheaf isomorphisms must consume those very module equivalences.

Constructed and justification: RootFractionalSheaf.iso composes the actual old global-sheaf local pullback with tilde(equivalence), and records the entire hom composite. InfinityFractionalSheaf.iso uses the exact old local frame and its explicit fractional module frame. No arbitrary replacement object is used.

## 9. Boundary and attribution

Required: Local isomorphisms do not prove the global embedded sheaf or associated-divisor comparison.

Constructed and justification: Eight fresh modules extend1329 exact predecessors and explicitly credit baseline TildePullback/IdentityCotangent/ScalarExtensionTensor and existing ideal localization/frame producers. Canonical Spec(stalk) comparison, cross-chart generic embedding compatibility, all-open valuation-section equality and theta/Weil identification remain separate. No local Lean or recovered historical acceptance is asserted.
