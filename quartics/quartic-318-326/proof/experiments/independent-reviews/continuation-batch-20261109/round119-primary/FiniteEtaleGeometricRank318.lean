module
public import FiniteEtaleFieldPoints318
public import CartesianSectionPoints318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public section
noncomputable section
namespace FiniteEtaleGeometricRank318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [IsAlgClosed F]
variable {X : Scheme} (f : X ⟶ Spec (CommRingCat.of F)) [IsFinite f] [Etale f]
/-- Actual sections of any finite-etale Scheme over an algebraically closed field
have cardinality equal to the actual structural rank. -/
theorem card_sections_eq_rank :
    Nat.card {s : Spec (CommRingCat.of F) ⟶ X // s ≫ f = 𝟙 _} =
      f.finrank (IsLocalRing.closedPoint F) := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  let e := X.isoSpec
  obtain ⟨φ,hφ⟩ := Spec.map_surjective (e.inv ≫ f)
  letI : Algebra F (Scheme.Γ.obj (Opposite.op X)) := φ.hom.toAlgebra
  have he : e.inv ≫ f = Spec.algebraMap F (Scheme.Γ.obj (Opposite.op X)) := hφ.symm
  haveI : IsFinite (Spec.algebraMap F (Scheme.Γ.obj (Opposite.op X))) := he ▸ inferInstance
  haveI : Etale (Spec.algebraMap F (Scheme.Γ.obj (Opposite.op X))) := he ▸ inferInstance
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have het : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  letI : Module.Finite F (Scheme.Γ.obj (Opposite.op X)) := by
    apply RingHom.finite_algebraMap.mp
    exact (IsFinite.SpecMap_iff φ).mp hfin
  letI : Algebra.Etale F (Scheme.Γ.obj (Opposite.op X)) := by
    apply RingHom.etale_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @Etale) (φ := φ)).mp het
  have hh : e.hom ≫ Spec.algebraMap F (Scheme.Γ.obj (Opposite.op X)) = f := by
    rw [←he]
    simp
  calc
    Nat.card {s : Spec (CommRingCat.of F) ⟶ X // s ≫ f = 𝟙 _} =
        Nat.card (FiniteEtaleFieldPoints318.Points F (Scheme.Γ.obj (Opposite.op X))) :=
      Nat.card_congr (CartesianSectionPoints318.isoEquiv e f _ hh)
    _ = Module.finrank F (Scheme.Γ.obj (Opposite.op X)) := FiniteEtaleFieldPoints318.card_points _ _
    _ = (Spec.algebraMap F (Scheme.Γ.obj (Opposite.op X))).finrank (IsLocalRing.closedPoint F) := by
      rw [Scheme.Hom.finrank_SpecMap_algebraMap,Module.rankAtStalk_eq_finrank_of_free]
      rfl
    _ = f.finrank (IsLocalRing.closedPoint F) := by
      rw [←he,Scheme.Hom.finrank_comp_left_of_isIso]
end FiniteEtaleGeometricRank318
