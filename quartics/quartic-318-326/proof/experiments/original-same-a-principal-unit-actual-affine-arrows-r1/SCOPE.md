# Actual normalized principal-unit reduction: affine arrows, split and boundary

Four new Lean owners; all previous donors byte-identical:

1. ActualAffineArrows works on a genuine affine subopen of a normalized
   frame, using that same global epsilon injection and same derived
   reduction. The original constant affine charts give the actual
   constant, reduction and epsilon scalar equations, so the arrow
   coefficients are exactly inr and fst. The two original closed affine
   reductions are identified via the actual projections, not two models.
2. ActualAffineAmbientTop transports restricted Spec top sections to
   the same ambient sections. It proves the exact scalar inverse using
   the induced map of equal actual opens and scheme appLE, and proves
   the actual Γ map compatibility by sheaf naturality.
3. AffineTopRow forms the two true linear coordinate equivalences,
   proves Γ of both actual arrows equals the marked affine split,
   restricts the original given line frame to the actual D-affine,
   and transports back through the natural affine tilde counit on
   the three unchanged sheaves. No arrow calibration or ShortExact
   hypothesis appears in affine_split.
4. AffineCoverExact derives the intrinsic original affine basis
   refining the actual frame cover, with structure k-algebras from
   the actual original morphism. On every chart the true D-chart is
   produced by constantAffineMap. The strict stalk local split
   criterion then gives the actual additive ShortExact. The same
   row now supplies its boundary on 1 and the +p overlap value.
   A separate entry accepts a genuine atlas without requiring a split.

The assumptions describe the literal normalized line on the actual
constant scheme, its genuine frame cover and its actual positive
principal-unit transitions. The source does not build PEL or the
normalized Poincare line, and does not prove any equality with old KS.
The actual derivative/positive-line coefficients remain the separate
paper and source facts that instantiate the literal transitions.
No local Lean, hosted, dispatch, push, or compiled claim.
