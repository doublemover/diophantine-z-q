module
public import ThreeTorsionFunctor318
public import TwoTorsionCurve318
public section
noncomputable section
namespace ThreeTorsionScheme318
open CategoryTheory AlgebraicGeometry Polynomial ThreeTorsionAlgebra318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

@[expose] def coordinateMap : ShortAffineJacobian318.Ring A B→ₐ[R]Ring A B hD :=
  AffineEquationFunctor318.toHom A B ⟨(x A B hD,y A B hD),by
    change (y A B hD)^2-(x A B hD)^3-algebraMap R (Ring A B hD) A*x A B hD-
      algebraMap R (Ring A B hD) B=0
    linear_combination equation A B hD⟩
lemma coordinateMap_x : coordinateMap A B hD (ShortAffineJacobian318.x A B)=x A B hD :=
  AffineEquationFunctor318.toHom_x _ _ _
lemma coordinateMap_y : coordinateMap A B hD (ShortAffineJacobian318.y A B)=y A B hD :=
  AffineEquationFunctor318.toHom_y _ _ _

@[expose] def scheme : Scheme:=Spec (CommRingCat.of (Ring A B hD))
@[expose] def structureMap : scheme A B hD⟶Spec (CommRingCat.of R):=
  Spec.map (CommRingCat.ofHom (algebraMap R (Ring A B hD)))
@[expose] def inclusion : scheme A B hD⟶ShortAffineScheme318.scheme A B:=
  Spec.map (CommRingCat.ofHom (coordinateMap A B hD).toRingHom)

theorem inclusion_over_base : inclusion A B hD≫ShortAffineScheme318.structureMap A B=
    structureMap A B hD:=by
  unfold inclusion ShortAffineScheme318.structureMap structureMap scheme ShortAffineScheme318.scheme
  rw [←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (coordinateMap A B hD).comp_algebraMap

theorem finite_etale : IsFinite (structureMap A B hD) ∧ Etale (structureMap A B hD):=by
  letI:=ThreeTorsionAlgebra318.finite A B hD
  letI:=ThreeTorsionAlgebra318.etale A B hD
  constructor
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)

theorem flat_surjective [Nontrivial R] :
    Flat (structureMap A B hD) ∧ Surjective (structureMap A B hD) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr (ThreeTorsionAlgebra318.faithfullyFlat A B hD)

end ThreeTorsionScheme318
