# Projective morphism of the actual bicanonical pair

This packet constructs the projective Scheme morphism of the already checked
global sections q0 and q1, proves their rational linear independence, and binds
the map's degree-sixteen calculation to its actual affine base change. All
statements retain arbitrary rational unit twists c : Fin 4 → Qˣ.

## Construction and actual objects

The target is the existing genuine projective-line Scheme. The homogeneous
coordinate convention is [q1:q0]: its finite coordinate is q1/q0=t, and its
opposite coordinate is q0/q1=s=u²/c0, where u=c0/y0.

1. `ContactBicanonicalRatios318` forms the ratios by multiplying by the inverse
   of the actual unit coefficient: q0 on every branch chart and q1 on the
   entire infinity chart. It proves that these are exactly t and u²/c0.
   No branch coordinate z_i or infinity coordinate u is inverted here.
2. `ContactBicanonicalSectionRatios318` proves the ratio equations for the
   actual global sections restricted to the corresponding full chart images.
   The generation theorem makes each ratio unique in the actual structure
   sheaf. Thus these are the ratios of the actual pair, not merely plausible
   coordinate formulas.
3. `ContactBicanonicalProjectiveMap318` evaluates the polynomial coordinate at
   those ratios, composes with the two genuine projective-line charts, and
   glues these Scheme morphisms over the actual five-chart open cover. The
   already checked contact-line morphism proves their compatibility on the
   categorical intersections; it is not assumed to be the map being defined.
   `projectiveMap_eq` then proves equality as Scheme morphisms with the actual
   normalization map. `projectiveMap_finite` and `.projectiveMap_proper` follow.
4. `ContactBicanonicalIndependence318.global_linear_independent` says that
   a*q0+b*q1=0 implies a=b=0 for rational a,b. Constants are explicitly mapped
   by the actual Q-structure morphism. Restriction to an actual branch chart,
   generation by q0, and the ratio identity give a+b*t=0. The exact specified
   embeddings into the original full field make polynomial evaluation at t
   injective, and coefficient extraction finishes the argument.
5. `ContactBicanonicalDegree318.affine_pullback` identifies the entire actual
   base change to the standard t-chart with Spec(SourceOrder c), through the
   actual source chart embedding and polynomial algebra map. The coordinate
   algebra is finite free of rank sixteen on this whole chart, including the
   four finite contacts. `genericFiberEquiv` identifies its rational-function
   base change with the specified original full field; `.generic_degree_sixteen`
   gives dimension sixteen over Q(t).

## Exact degree scope

The packet proves an actual cartesian t-chart square, finite-free rank sixteen
there, and the specified generic-fiber algebra equivalence and degree sixteen.
These give the map's generic degree sixteen. It does not introduce a numeric
Scheme-degree API or separately prove local freeness/rank on every infinity
neighborhood. It does not compute a canonical divisor degree or genus.

## Retained boundaries

This is a two-dimensional base-point-free subspace of the genuine intrinsic
bicanonical sections. It is not claimed to be the complete bicanonical linear
system or a bicanonical embedding. No new isomorphism with the pullback of O(1),
choice of the arbitrary twists from a Shimura/PEL source, PEL identification,
Kodaira–Spencer comparison, metric normalization, or height bound is asserted.
The construction uses the direct universal-coordinate global section names
from the frozen predecessor; no failed legacy inverse-frame alias is imported.

## Verification and review

The five sources are freshly replayed with kernel checking enabled, followed
by a joined recursive axiom audit of these and the fifty immediate earlier
contact/tensor/gluing/generation modules. Exact source and dependency hashes,
results and the nine application obligations are recorded separately. This is
a bounded packet replay, not a clean whole-repository rebuild. Independent
non-author application review remains a separate required record.
