module
public import SelectedSignedMultiplication318
public import SelectedPrimitiveOpen318
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Set WeierstrassGluing318
open SelectedSignedMultiplication318 SelectedCompletedMultiplication318
open SelectedLiteralTorsionKernel318 LiteralSchemePointOperations318

namespace SelectedLiteralMarkedScaling318
variable (n : ℕ)
local notation "a" => OpenJAffineScheme318.A n
local notation "b" => OpenJAffineScheme318.B n
local notation "g" => OpenJAffineScheme318.discriminant_unit n

theorem literal_test (k : ℕ) {T : Scheme} (j : T ⟶ Base n) (P : Points n j) :
    Killed g k P.val ↔ k • P = 0 := by
  have he : P.val ≫ structureMap a b = j := P.property
  change P.val ≫ mul a b g k = (P.val ≫ structureMap a b) ≫ infinity a b ↔ _
  rw [literal_eval n k j P,he]
  constructor
  · intro hz
    apply Subtype.ext
    exact hz
  · intro hz
    exact congrArg Subtype.val hz

theorem literal_tests_order (m : ℕ) (hm : 0 < m) {T : Scheme}
    (j : T ⟶ Base n) (P : Points n j) : ExactTests g m P.val ↔ addOrderOf P = m := by
  constructor
  · intro h
    have hd : addOrderOf P ∣ m :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((literal_test n m j P).mp h.1)
    have hp : 0 < addOrderOf P := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz,zero_dvd_iff] at hd
      exact (Nat.ne_of_gt hm) hd
    apply le_antisymm (Nat.le_of_dvd hm hd)
    by_contra! hh
    exact h.2 (addOrderOf P) hp hh
      ((literal_test n (addOrderOf P) j P).mpr (addOrderOf_nsmul_eq_zero P))
  · intro h
    refine ⟨(literal_test n m j P).mpr ?_,?_⟩
    · rw [←h]
      exact addOrderOf_nsmul_eq_zero P
    · intro k hk hkm hz
      have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((literal_test n k j P).mp hz)
      rw [h] at hd
      exact (Nat.not_le_of_gt hkm) (Nat.le_of_dvd hk hd)

variable (A B : OpenJModel318.Base n) (r : (OpenJModel318.Base n)ˣ)
variable (hA : A = (r:OpenJModel318.Base n)^4*a) (hB : B = (r:OpenJModel318.Base n)^6*b)
local notation "γ" => SelectedPointedShortScaling318.gluedMap A B a b r hA hB
local notation "g₁" => SelectedCompletedAdditiveScaling318.target_smooth_disc A B a b r hA hB g

/-- For the actual primitive locus and the same actual kernel point, every
positive lower-order test is preserved by the pointed scaling. This statement
uses a singleton test, as required to read membership in a primitive open;
it does not confuse exact global order with fiberwise primitivity on a
disconnected Scheme. -/
theorem primitive_point_iff (m : ℕ) (hm : 0 < m)
    [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]
    {T : Scheme} [Subsingleton T] (P : T ⟶ Kernel n m) (x : T) :
    P x ∈ SelectedPrimitiveOpen318.primitive n m ↔
      ExactTests g₁ m ((P ≫ inclusion n m) ≫ γ) := by
  rw [SelectedPrimitiveOpen318.primitive_iff_order n m P x hm,
    exact_tests_iff A B a b r hA hB g m (P ≫ inclusion n m)]
  exact (literal_tests_order n m hm (P ≫ kernelProjection n m) (pointOf n m P)).symm

end SelectedLiteralMarkedScaling318

#print axioms SelectedLiteralMarkedScaling318.literal_tests_order
#print axioms SelectedLiteralMarkedScaling318.primitive_point_iff
