module
public import PELOriginalLevelMarkings318
public section
noncomputable section
namespace PELLevelThreeSimilitudes318
open PELOrderReductionThree318 PELPrincipalOrderCoordinates318
open PELReductionResidueField318 PELActualLevelThreeQuotient318
open PELOriginalThreeTorsion318 PELOriginalLevelMarkings318
set_option maxHeartbeats 1200000

/-- The exact original reduced norm on the integral order coordinates. -/
@[expose] def integralNorm (a : Coordinates) : ℤ :=
  a 0^2+a 0*a 2+210*a 1^2+210*a 1*a 3-a 2^2+42*a 3^2

theorem original_norm (a : Coordinates) :
    PELQuaternionAlgebra318.reducedNorm (embed a)=(integralNorm a:ℚ) := by
  simp [PELQuaternionAlgebra318.reducedNorm,embed,integralNorm] <;> push_cast <;> ring

/-- Reduced norm on the actual finite order quotient is the norm of its
actual F9 residue, retaining all original order-coordinate normalization. -/
@[expose] def norm (a : QuotientOrder) : F3 := QuadraticAlgebra.norm (quotientResidue a)

theorem norm_original (a : Coordinates) :
    norm (moduloThree.mk' (coordinatesEquiv a))=(integralNorm a:F3) := by
  change QuadraticAlgebra.norm (residue (quotientEquiv (moduloThree.mk' (coordinatesEquiv a))))=_
  rw [quotientEquiv_mk,reduction_coordinates]
  have h3 : (3:F3)=0 := by decide
  simp [residue,reduceCoordinates,QuadraticAlgebra.norm_def,integralNorm] <;>
    push_cast <;> norm_num
  linear_combination (-(a 0:F3)*(a 2:F3)-70*(a 1:F3)^2-
    70*(a 1:F3)*(a 3:F3)-14*(a 3:F3)^2)*h3

/-- Right multiplication is a similitude by the ORIGINAL reduced norm,
not automatically an isometry. This is an integer polynomial identity. -/
theorem integral_right_similitude (a b c : Coordinates) :
    integralForm (product a c) (product b c)=integralNorm c*integralForm a b := by
  simp [integralForm,product,integralNorm] <;> ring

theorem right_similitude (a b c : QuotientOrder) :
    PELLevelThreeAlternatingPair318.pair (a*c) (b*c)=
      norm c*PELLevelThreeAlternatingPair318.pair a b := by
  obtain ⟨a,rfl⟩ := moduloThree.mk'_surjective a
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective a
  obtain ⟨b,rfl⟩ := moduloThree.mk'_surjective b
  obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective b
  obtain ⟨c,rfl⟩ := moduloThree.mk'_surjective c
  obtain ⟨c,rfl⟩ := coordinatesEquiv.surjective c
  rw [← map_mul moduloThree.mk' (coordinatesEquiv a) (coordinatesEquiv c),
    ← map_mul moduloThree.mk' (coordinatesEquiv b) (coordinatesEquiv c),
    ← coordinates_mul a c,← coordinates_mul b c,
    PELLevelThreeAlternatingPair318.original_pair,
    PELLevelThreeAlternatingPair318.original_pair,norm_original,integral_right_similitude]
  push_cast <;> ring

theorem unit_norm_ne_zero (u : QuotientOrderˣ) : norm (u:QuotientOrder)≠0 := by
  intro h
  apply (u.isUnit.map quotientResidue).ne_zero
  exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h

variable (τ : ℂ) (hτ : 0<τ.im)

/-- Exact polarization multiplier of every actual order-compatible marking
change. Full72 units are retained; a norm-one condition has not been inserted. -/
theorem original_marking_similitude (u : QuotientOrderˣ) (x y : torsion τ) :
    PELPeriodTorsionPolarization318.pair τ hτ ((unitsEquiv τ hτ u).val x)
      ((unitsEquiv τ hτ u).val y)=
      norm (u:QuotientOrder)*PELPeriodTorsionPolarization318.pair τ hτ x y := by
  rw [unitsEquiv_value,unitsEquiv_value]
  simp only [PELPeriodTorsionPolarization318.pair,AddEquiv.symm_apply_apply]
  exact right_similitude _ _ _

/-- Every actual marking automorphism is a similitude with a specified
nonzero finite multiplier; no arithmetic/Galois action is assumed constructed. -/
theorem every_original_marking (f : MarkingAutomorphisms τ) :
    ∃ m : F3, m≠0 ∧ ∀ x y : torsion τ,
      PELPeriodTorsionPolarization318.pair τ hτ (f.val x) (f.val y)=
        m*PELPeriodTorsionPolarization318.pair τ hτ x y := by
  obtain ⟨u,rfl⟩ := (unitsEquiv τ hτ).surjective f
  exact ⟨norm (u:QuotientOrder),unit_norm_ne_zero u,original_marking_similitude τ hτ u⟩
end PELLevelThreeSimilitudes318
