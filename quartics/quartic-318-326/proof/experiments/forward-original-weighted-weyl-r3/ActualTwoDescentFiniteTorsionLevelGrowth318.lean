module
public import ActualTwoDescentActualHigherSelmerFinite318
public section
noncomputable section
namespace ActualTwoDescentFiniteTorsionLevelGrowth318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology

open ActualTwoDescentHigherMultiplesTransport318
variable (T : Type*) [AddCommGroup T] [Finite T]

lemma actual_torsion_kernel_mono {i j : ℕ} (hij : i ≤ j) :
    torsionKernel T (2^i) ≤ torsionKernel T (2^j) := by
  intro x hx
  obtain ⟨a,ha⟩ := Nat.pow_dvd_pow 2 hij
  change (2^j) • x=0
  rw [ha,mul_comm,mul_smul]
  have h : (2^i) • x=0 := hx
  rw [h,nsmul_zero]

lemma actual_torsion_kernel_card_monotone : Monotone (fun k : ℕ => Nat.card (torsionKernel T (2^k))) := by
  intro i j hij
  let f : torsionKernel T (2^i) → torsionKernel T (2^j) := fun x => ⟨x.val,actual_torsion_kernel_mono T hij x.property⟩
  exact Nat.card_le_card_of_injective f (fun x y h => Subtype.ext (congrArg Subtype.val h))

lemma actual_torsion_kernel_card_bound (k : ℕ) : Nat.card (torsionKernel T (2^k)) ≤ Nat.card T :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end ActualTwoDescentFiniteTorsionLevelGrowth318
