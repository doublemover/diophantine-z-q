# Original-ring residues and actual source H1 independence

This65-source packet is uncompiled. Hosted strict Lean checks, recursive axiom
auditing and independent acceptance are pending. Its59 dependencies are exact
copies of character-action-r1. No local Lean build was run. The six new modules
form one end-to-end construction, not a dimension conclusion from formal labels.

OriginalInfinityCoefficient318 applies the actual infinity basis coefficient map
and the original infinityPoint evaluation at u=0. It computes the rational value
on each actual infinity monomial and kills multiplication by the actual u. The
original infinity-to-overlap inclusion is proved injective through the already
specified original field embeddings.

OriginalNegativePoleUniqueness318 multiplies any finite negative-pole combination
by u^N to put it in the original infinity ring. Evaluating its basis coefficients
at u=0 isolates the highest-pole coefficient. If the combination was infinity-
regular, that coefficient is zero. Induction removes every coefficient. All
eight basis indices and every pole up to N are retained; the empty case is
included. Thus a nonzero negative principal part cannot secretly be regular.

OriginalOverlapResidues318 packages arbitrary finite negative coefficients as a
Finsupp indexed by (pole-1, original infinity monomial). It uses an explicit finite
rectangle bound to apply the uniqueness theorem. Whole-overlap principal
reduction proves the joint map (negative coefficients, actual infinity element)
is surjective. Its kernel has zero coefficient component, so lifting the first
projection defines canonical full residue coefficients on the original overlap.
The residue map is proved inverse to negative evaluation and zero on the whole
infinity image. No Laurent-series field or unproved comparison replaces the ring.

OriginalFinitePoleExpansion318 expands every element of the original finite
chart using all16 basis entries and every polynomial coefficient. Each term maps
to the original infinity monomial with exact pole order 2m+totalWeight and exact
rational scalar q*c0^(m+totalWeight). That pole order is at least the infinity
monomial weight. The root-zero, other-root and t transitions are proved through
the original field embeddings and then reflected into the actual overlap ring.

OriginalSmallPoleResidues318 selects the five positive poles below their weights.
Every high pole has zero selected residues; zero poles vanish through the actual
infinity image. The full finite expansion therefore proves these residues kill
every element of the whole finite image too. Each small representative has its
literal Kronecker residue, and the full five-representative map has residue q.

ActualSourceHOneResidueBasis318 uses the exact original boundary kernel equality
to descend these five functionals to the unchanged structural rational H1. Their
pairing with the exact previously constructed fiveLinear map is the identity.
This supplies injectivity as well as the prior whole-H1 surjectivity. The proposed
endpoint is an unconditional rational equivalence Q^SmallIndex -> actual source
H1 with the constructed residueMap as inverse, and genuine source finrank5. It
also proves the five original root-character cohomology classes nonzero, thereby
discharging CoordinatesNonzero for the actual projector decomposition.

These are proposed Lean theorem statements awaiting compilation and review, not
claims of completed validation. The proof still does not identify the five
original quotient-H1 pullback images with these five source character lines.
In particular the quotient-induced source sign action has not been compared to
the functorial sheaf pullbacks used by those maps. That geometric naturality and
exact quotient-class comparison remain needed for the original five-map endpoint.
Nonzero coordinate classes do not by themselves prove nonzero target H1 or the
cross-transfer identities. No such inference is made here.

## Revision r2

Hosted run42578244224 at aa07a2c passed the section-kernel module and all32
predecessors, then failed an implicit rewrite in AffineCoverHOneQuotient318
across the structure-sheaf component versus original ring-section carrier.
The only changed Lean source now invokes sectionBoundary_kernel with the
explicit original sheaf, opens, cover and element; a typed change exposes the
original ring restrictions, then the same pair-of-witnesses equivalence is
composed directly. No maps, kernels, sections or signs change. Original tested
55-source bytes/logs remain in rational-exhaustion-r2/hosted-failure-aa07a2c.
The entire revised65-source closure remains pending hosted checks and review.
