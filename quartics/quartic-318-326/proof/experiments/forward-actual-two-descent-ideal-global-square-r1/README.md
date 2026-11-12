# Actual original global tensor-square trivialization

Six new sources preserve all1286 predecessor Lean sources. For the original native ideal sheaf M=originalRootIdealSheaf(n,i),over any characteristic-zero field and n!=0,the packet constructs

IntrinsicTensorSheaf.tensor M M ≅ SheafOfModules.unit(originalCubicScheme(n)).

This is a genuine native sheaf isomorphism on the SAME original global cubic scheme. Its forward map and inverse are separately glued by the existing ModuleLocalIsomorphism318.iso producer,and both inverse equations are provided. The local formula retains exactly the OLD scaled chart squares: inverse pole coefficient at infinity and the actual root-local coefficients on both principal affine charts.

The new connection is chart-to-AMBIENT local data. For any actual open immersion and any original ambient subopen inside its image,the native structure map is an explicit ring isomorphism. Composing the chart-map adjoint with its inverse gives a linear map over the actual ambient section ring. Native adjoint and structure-map naturality prove all-subopen naturality. A genuine chart isomorphism gives bijectivity on every such subopen because the adjunction unit is restriction along equality of opens.

Exact refinement invariance identifies those ambient coordinates with the canonical common-chart coordinate. The actual three-chart atlas,complete pairwise-intersection equalities and all three OLD square restrictions from the predecessors then produce compatibility,not a compatibility hypothesis. The original n!=0 cover theorem supplies the precise global domain. Existing native map/inverse gluing yields originalGlobalSquare,with an exact formula on every original ambient subopen of each old chart.

Boundary: this constructs a global square-trivialization of the actual native line sheaf already built from the root ideal and b/u matching. It does NOT yet identify that sheaf with a named projective Cartier/Weil divisor or identify its translation action with the geometric theta group/Weil pairing. Brauer invariants,reciprocity,Cassels--Tate and the final rank theorem remain separate. No local Lean or cap changes;distinct source review and hosted kernel acceptance pending.
