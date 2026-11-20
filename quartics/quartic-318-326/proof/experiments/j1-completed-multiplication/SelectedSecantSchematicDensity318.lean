module
public import RelativeChordScheme318
public import AffineBaseChange318
public import AffineCoordinateDomain318
public import SpecSchematicDensity318
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open RelativeChordAlgebra318

namespace SelectedSecantSchematicDensity318
variable {R : Type u} [CommRing R] (A B : R)
local notation "S" => ShortAffineJacobian318.Ring A B
local notation "a" => algebraMap R S
local notation "W" => AffineCoordinateDomain318.model (a A) (a B)
local notation "T" => AffineCoordinateDomain318.CoordinateRing (a A) (a B)

/-- The actual tensor self-product, read as the same equation of the
second factor over the first factor. -/
@[expose] def secondOverFirst : PairRing A B ≃ₐ[S] T :=
  (AffineBaseChange318.baseChangeEquiv (S := S) A B).trans
    (AffineCoordinateDomain318.coordinateEquiv (a A) (a B))

private theorem secondOverFirst_left (z : S) :
    secondOverFirst A B (leftPair A B z) = algebraMap S T z := by
  change secondOverFirst A B (algebraMap S (PairRing A B) z) = _
  exact AlgEquiv.commutes _ z

private theorem secondOverFirst_right_x :
    secondOverFirst A B (rightPair A B (ShortAffineJacobian318.x A B)) =
      AffineCoordinateDomain318.x (a A) (a B) := by
  change AffineCoordinateDomain318.coordinateEquiv (a A) (a B)
    (AffineBaseChange318.baseChangeEquiv (S := S) A B
      (1 ⊗ₜ[R] ShortAffineJacobian318.x A B)) = _
  rw [AffineBaseChange318.baseChangeEquiv_x] <;> exact AffineCoordinateDomain318.forward_x _ _

theorem gap_as_monic_scalar :
    secondOverFirst A B (gap A B) =
      algebraMap (Polynomial S) T (Polynomial.X - Polynomial.C (ShortAffineJacobian318.x A B)) := by
  have hc (z : S) : algebraMap (Polynomial S) T (Polynomial.C z) = algebraMap S T z := by
    rw [AdjoinRoot.algebraMap_eq' S,Polynomial.algebraMap_eq] <;> rfl
  rw [gap,map_sub,map_sub,secondOverFirst_left,secondOverFirst_right_x,hc] <;> rfl

/-- x₂−x₁ is regular in the exact tensor chart over every commutative ring,
even with nilpotents. It is monic in the second abscissa and acts on a
free module over that polynomial line. -/
theorem gap_regular : gap A B ∈ nonZeroDivisors (PairRing A B) := by
  have hmonic : W.polynomial.Monic := by
    rw [AffineCoordinateDomain318.polynomial_formula]
    exact Polynomial.monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  letI : Module.Free (Polynomial S) T := hmonic.free_adjoinRoot
  rw [mem_nonZeroDivisors_iff_left]
  intro z hz
  apply (secondOverFirst A B).injective
  rw [map_zero]
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := T)
    (Polynomial.monic_X_sub_C (ShortAffineJacobian318.x A B)).mem_nonZeroDivisors
  simp only [Algebra.smul_def]
  simpa only [map_mul,map_zero,mul_zero,gap_as_monic_scalar] using congrArg (secondOverFirst A B) hz

theorem localization_injective :
    Function.Injective (algebraMap (PairRing A B) (ChordRing A B)) := by
  apply IsLocalization.injective (M := Submonoid.powers (gap A B))
  rintro z ⟨n,rfl⟩
  exact (nonZeroDivisors (PairRing A B)).pow_mem (gap_regular A B) n

theorem dense : IsSchemeTheoreticallyDominant (RelativeChordScheme318.intoProduct A B) := by
  letI := SpecSchematicDensity318.spec_of_injective
    (CommRingCat.ofHom (algebraMap (PairRing A B) (ChordRing A B)))
    (localization_injective A B)
  unfold RelativeChordScheme318.intoProduct
  infer_instance

end SelectedSecantSchematicDensity318

#print axioms SelectedSecantSchematicDensity318.gap_regular
#print axioms SelectedSecantSchematicDensity318.dense
