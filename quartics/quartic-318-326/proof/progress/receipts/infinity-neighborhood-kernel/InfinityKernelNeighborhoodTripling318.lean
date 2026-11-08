module
public import InfinityKernelNeighborhoodZero318
public import LiteralSchemeCancellation318
import all WeierstrassGluing318
public section
noncomputable section
namespace InfinityKernelNeighborhoodTripling318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinityKernelNeighborhoodScheme318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def originSection (A B:R) (h3:IsUnit (3:R)) : Spec (CommRingCat.of R) ⟶ scheme A B :=
  Spec.map (CommRingCat.ofHom (InfinityKernelNeighborhoodOrigin318.originLift A B h3).toRingHom)
@[reassoc] theorem originSection_intoCurve (A B:R) (h3:IsUnit (3:R)) :
    originSection A B h3 ≫ intoCurve A B=WeierstrassGluing318.infinity A B := by
  have he:(InfinityKernelNeighborhoodOrigin318.originLift A B h3).comp
      (InfinityKernelNeighborhoodAlgebra318.input A B)=InfinityChart318.origin A B := by
    apply AlgHom.ext
    exact InfinityKernelNeighborhoodOrigin318.originLift_input A B h3
  change Spec.map (CommRingCat.ofHom (InfinityKernelNeighborhoodOrigin318.originLift A B h3).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (InfinityKernelNeighborhoodAlgebra318.input A B).toRingHom) ≫
      WeierstrassGluing318.infinityChart A B)=_
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((InfinityKernelNeighborhoodOrigin318.originLift A B h3).comp
    (InfinityKernelNeighborhoodAlgebra318.input A B)).toRingHom) ≫ _=_
  rw [he]
  rfl
@[reassoc] theorem originSection_structure (A B:R) (h3:IsUnit (3:R)) :
    originSection A B h3 ≫ structureMap A B=𝟙 _ := by
  rw [structureMap,←Category.assoc,originSection_intoCurve,WeierstrassGluing318.infinity_section]

/-- The actual literal tripling kernel is exactly the zero section on the
genuine principal-open neighborhood, for every Scheme test object. -/
theorem scheme_zero (N:ℕ) {X:Scheme}
    (x:X ⟶ scheme (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
    (h:x ≫ intoCurve (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
        CompletedIteratedAddition318.tripling (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
          (OpenJAffineScheme318.discriminant_unit N)=
      x ≫ structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
        WeierstrassGluing318.infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) :
    x ≫ intoCurve (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)=
      x ≫ structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
        WeierstrassGluing318.infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) := by
  apply InfinityKernelNeighborhoodZero318.scheme_zero _ _ (OpenJAffineScheme318.discriminant_unit N) x
  have hc:=(LiteralSchemeCancellation318.tripling_zero_iff N
    (x ≫ intoCurve (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))).mp
    (by simpa only [Category.assoc,structureMap] using h)
  simpa only [Category.assoc] using hc
end InfinityKernelNeighborhoodTripling318
