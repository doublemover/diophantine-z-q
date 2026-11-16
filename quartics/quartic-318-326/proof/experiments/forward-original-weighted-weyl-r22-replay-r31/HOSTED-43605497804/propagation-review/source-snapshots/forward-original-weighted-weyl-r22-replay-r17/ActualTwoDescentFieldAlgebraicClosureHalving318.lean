module
public import ActualTwoDescentActualCohomologicalImage318
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public section
noncomputable section
namespace ActualTwoDescentFieldAlgebraicClosureHalving318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentKummerHom318 ActualTwoDescentRootKummerHom318
open ActualTwoDescentKummerFullKernel318
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]

lemma actual_closed_class_one (a : K) (ha : a ≠ 0) : classOf a ha=1 := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < (2 : ℕ))
  have hsn : s ≠ 0 := by intro h; subst s; simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs; exact ha hs.symm
  rw [←class_of_one]
  exact (class_of_eq_iff a 1 ha one_ne_zero).mpr ⟨s,hsn,by simpa only [one_mul] using hs.symm⟩

/-- Actual surjectivity of doubling on the original curve over an algebraically closed field. -/
theorem actual_closed_halving (n : K) (hn : n ≠ 0) (P : Point n) : ∃ Q : Point n, Q+Q=P := by
  apply (actual_kummer_kernel n hn P).mp
  apply Prod.ext
  · exact actual_closed_class_one _ _
  · exact actual_closed_class_one _ _

local instance : DecidableEq Qbar := Classical.decEq _

lemma rational_parameter_ne (n : F) (hn : n ≠ 0) : algebraMap F Qbar n ≠ 0 :=
  ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero (algebraMap F Qbar) hn

def actualHalf (n : F) (hn : n ≠ 0) (P : Point (algebraMap F Qbar n)) : Point (algebraMap F Qbar n) :=
  Classical.choose (actual_closed_halving _ (rational_parameter_ne n hn) P)

lemma actual_half_spec (n : F) (hn : n ≠ 0) (P : Point (algebraMap F Qbar n)) :
    actualHalf n hn P+actualHalf n hn P=P :=
  Classical.choose_spec (actual_closed_halving _ (rational_parameter_ne n hn) P)

end ActualTwoDescentFieldAlgebraicClosureHalving318
