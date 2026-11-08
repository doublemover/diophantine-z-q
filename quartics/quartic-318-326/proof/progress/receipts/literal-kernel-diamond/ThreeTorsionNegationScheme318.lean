module
public import ThreeTorsionInvolution318
public import ThreeTorsionCompletedDoubling318
public section
noncomputable section
namespace ThreeTorsionNegationScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)] (hD:IsUnit (-16*(4*A^3+27*B^2)))

/-- The original rank-eight algebra involution, viewed as its actual Scheme map. -/
@[expose] def negation : ThreeTorsionScheme318.scheme A B hD ⟶ ThreeTorsionScheme318.scheme A B hD :=
  Spec.map (CommRingCat.ofHom (ThreeTorsionInvolution318.negHom A B hD).toRingHom)
lemma coordinate_compatibility :
    (ThreeTorsionInvolution318.negHom A B hD).comp (ThreeTorsionScheme318.coordinateMap A B hD)=
      (ThreeTorsionScheme318.coordinateMap A B hD).comp (ChartNegation318.affineNeg A B) := by
  apply WeierstrassOverlap318.affine_hom_ext
  · simp only [AlgHom.comp_apply,ThreeTorsionScheme318.coordinateMap_x,
      ThreeTorsionInvolution318.negHom_x,ChartNegation318.affineNeg_x]
  · simp only [AlgHom.comp_apply,ThreeTorsionScheme318.coordinateMap_y,
      ThreeTorsionInvolution318.negHom_y,ChartNegation318.affineNeg_y,map_neg]
@[reassoc] theorem finite_inclusion : negation A B hD ≫ ThreeTorsionScheme318.inclusion A B hD=
    ThreeTorsionScheme318.inclusion A B hD ≫ GluedNegation318.finiteNeg A B := by
  change Spec.map (CommRingCat.ofHom (ThreeTorsionInvolution318.negHom A B hD).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (ThreeTorsionScheme318.coordinateMap A B hD).toRingHom)=
    Spec.map (CommRingCat.ofHom (ThreeTorsionScheme318.coordinateMap A B hD).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (ChartNegation318.affineNeg A B).toRingHom)
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:ShortAffineJacobian318.Ring A B →ₐ[R] ThreeTorsionAlgebra318.Ring A B hD=>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (coordinate_compatibility A B hD)
@[reassoc] theorem completed_inclusion : negation A B hD ≫ ThreeTorsionCompletedDoubling318.inclusion A B hD=
    ThreeTorsionCompletedDoubling318.inclusion A B hD ≫ GluedNegation318.negation A B := by
  simp only [ThreeTorsionCompletedDoubling318.inclusion,Category.assoc,finite_inclusion_assoc,
    GluedNegation318.finiteChart_negation]
@[reassoc] theorem over_base : negation A B hD ≫ ThreeTorsionScheme318.structureMap A B hD=
    ThreeTorsionScheme318.structureMap A B hD := by
  change Spec.map (CommRingCat.ofHom (ThreeTorsionInvolution318.negHom A B hD).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (ThreeTorsionAlgebra318.Ring A B hD)))=_
  rw [←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (ThreeTorsionInvolution318.negHom A B hD).comp_algebraMap

theorem negation_twice : negation A B hD ≫ negation A B hD=𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (ThreeTorsionInvolution318.negHom A B hD).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ThreeTorsionInvolution318.negHom A B hD).toRingHom)=_
  dsimp only [ThreeTorsionScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (ThreeTorsionInvolution318.negHom_comp A B hD))
end ThreeTorsionNegationScheme318
