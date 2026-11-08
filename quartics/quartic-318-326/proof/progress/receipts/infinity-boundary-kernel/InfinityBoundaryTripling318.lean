module
public import InfinityClosedBoundary318
public import LiteralSchemeCancellation318
public section
noncomputable section
namespace InfinityBoundaryTripling318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- The actual literal tripling-zero condition cuts out exactly the origin
inside the possibly nonreduced z=0 boundary, for every coefficient algebra. -/
theorem tripling_zero_iff (N:ℕ) {S:Type} [CommRing S] [Algebra (OpenJModel318.Base N) S]
    (f:InfinityChart318.Ring (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) →ₐ[OpenJModel318.Base N] S)
    (hz:f (InfinityChart318.z (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))=0) :
    InfinityBoundaryScheme318.point (S:=S) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f ≫ CompletedIteratedAddition318.tripling (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)=
      InfinityBoundaryScheme318.point (S:=S) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f ≫ (WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) ≫ WeierstrassGluing318.infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ↔
    f=(Algebra.ofId (OpenJModel318.Base N) S).comp (InfinityChart318.origin (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) := by
  rw [LiteralSchemeCancellation318.tripling_zero_iff N]
  apply InfinityBoundaryScheme318.double_neg_iff (S:=S) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f hz (OpenJAffineScheme318.discriminant_unit N)
  simpa only [map_ofNat] using ((OpenJModel318.base_units N).2.1.map (algebraMap (OpenJModel318.Base N) S))
/-- Equivalent map-level formulation: on z=0, the actual tripling fiber
contains only the actual zero section, including nilpotent coefficient tests. -/
theorem tripling_zero_iff_point_zero (N:ℕ) {S:Type} [CommRing S] [Algebra (OpenJModel318.Base N) S]
    (f:InfinityChart318.Ring (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) →ₐ[OpenJModel318.Base N] S)
    (hz:f (InfinityChart318.z (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))=0) :
    InfinityBoundaryScheme318.point (S:=S) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f ≫ CompletedIteratedAddition318.tripling (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)=
      InfinityBoundaryScheme318.point (S:=S) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f ≫ (WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) ≫ WeierstrassGluing318.infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ↔
    InfinityBoundaryScheme318.point (S:=S) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f=
      InfinityBoundaryScheme318.point (S:=S) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f ≫ (WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) ≫ WeierstrassGluing318.infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) := by
  rw [tripling_zero_iff N f hz,←Category.assoc,InfinityBoundaryScheme318.point_over_base (S:=S),
    InfinityBoundaryScheme318.point_eq_zero_iff (S:=S)]

/-- The closed-boundary result for arbitrary test Schemes. This is an exact
restriction of the kernel, not yet an open-and-closed global decomposition. -/
theorem scheme_zero (N:ℕ) {X:Scheme}
    (x:X ⟶ InfinityClosedBoundary318.scheme (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
    (h:x ≫ InfinityClosedBoundary318.intoCurve (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
        CompletedIteratedAddition318.tripling (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
          (OpenJAffineScheme318.discriminant_unit N)=
      x ≫ InfinityClosedBoundary318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
        WeierstrassGluing318.infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) :
    x ≫ InfinityClosedBoundary318.intoCurve (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)=
      x ≫ InfinityClosedBoundary318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
        WeierstrassGluing318.infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) := by
  apply InfinityClosedBoundary318.scheme_zero _ _ (OpenJAffineScheme318.discriminant_unit N)
    (OpenJModel318.base_units N).2.1 x
  have hc:=(LiteralSchemeCancellation318.tripling_zero_iff N
    (x ≫ InfinityClosedBoundary318.intoCurve (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))).mp
    (by simpa only [Category.assoc,InfinityClosedBoundary318.intoCurve_base_assoc] using h)
  simpa only [Category.assoc] using hc

end InfinityBoundaryTripling318
