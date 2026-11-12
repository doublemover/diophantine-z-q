module
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Tactic
public section
noncomputable section
namespace JacobianKaehlerFrame318
open Algebra
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The genuine composed presentation after inverting the actual Jacobian. -/
@[expose] def localizedPresentation (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ Fin 2) (Unit ⊕ Unit) where
  toPreSubmersivePresentation := (PreSubmersivePresentation.localizationAway
    (Localization.Away P.jacobian) P.jacobian).comp P
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def]
    have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away P.jacobian) P.jacobian
    apply hu.mul
    change IsUnit (PreSubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian).jacobian
    rw [PreSubmersivePresentation.localizationAway_jacobian]
    exact hu

@[expose] def freeIndex (P : PreSubmersivePresentation R S (Fin 2) Unit) : Fin 2 :=
  (P.map ()).rev

lemma complement (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    IsCompl (Set.range (fun _ : Unit => (Sum.inr (freeIndex P) : Unit ⊕ Fin 2)))
      (Set.range (localizedPresentation P).map) := by
  have he : Set.range (fun _ : Unit => (Sum.inr (freeIndex P) : Unit ⊕ Fin 2)) =
      (Set.range (localizedPresentation P).map)ᶜ := by
    ext x
    cases x with
    | inl u => cases u; simp [localizedPresentation, PreSubmersivePresentation.comp_map]
    | inr i =>
      fin_cases i <;> generalize hi : P.map () = j <;> fin_cases j <;>
        simp [localizedPresentation, PreSubmersivePresentation.comp_map, freeIndex, hi]
  rw [he]
  exact IsCompl.symm isCompl_compl

/-- The actual differential of the unselected coordinate is a one-element basis. -/
@[expose] def basis (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    Module.Basis Unit (Localization.Away P.jacobian)
      (KaehlerDifferential R (Localization.Away P.jacobian)) :=
  (localizedPresentation P).basisKaehlerOfIsCompl (fun _ _ _ => Subsingleton.elim _ _) (complement P)

theorem basis_eq_differential (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    basis P () = KaehlerDifferential.D R (Localization.Away P.jacobian)
      (algebraMap S (Localization.Away P.jacobian) (P.val (freeIndex P))) := by
  rw [basis, SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

/-- The actual rank-one Kähler frame on the Jacobian localization. -/
@[expose] def frame (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    KaehlerDifferential R (Localization.Away P.jacobian) ≃ₗ[Localization.Away P.jacobian]
      Localization.Away P.jacobian :=
  (basis P).repr.trans (Finsupp.uniqueLinearEquiv _ _ ())

theorem frame_differential (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    frame P (KaehlerDifferential.D R (Localization.Away P.jacobian)
      (algebraMap S (Localization.Away P.jacobian) (P.val (freeIndex P)))) = 1 := by
  rw [←basis_eq_differential]
  simp [frame]

/-- The chosen coordinate differential generates the actual module. -/
theorem differential_generates (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    Submodule.span (Localization.Away P.jacobian)
      (Set.singleton (KaehlerDifferential.D R (Localization.Away P.jacobian)
        (algebraMap S (Localization.Away P.jacobian) (P.val (freeIndex P)))) :
          Set (KaehlerDifferential R (Localization.Away P.jacobian))) = ⊤ := by
  rw [←basis_eq_differential]
  convert (basis P).span_eq using 1
  congr 1
  ext ω
  simp [Set.singleton, Set.range_unique]

end JacobianKaehlerFrame318
