module
public import ActualTwoDescentFullBoundaryHom318
public section
noncomputable section
namespace ActualTwoDescentPowerValuedCocycles318
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

/-- Actual locally constant crossed cocycles valued in E[2^k], retained inside the full geometric representation. No trivial Galois action is asserted at higher levels. -/
def powerValuedCocycles (n : F) (hn : n ≠ 0) (k : ℕ) : AddSubgroup (continuousFullCocycles n hn) where
  carrier := {z | ∀ σ : Gal, (2^k) • z.val σ=0}
  zero_mem' σ := nsmul_zero _
  add_mem' hx hy σ := by change (2^k) • (_+_)=0; rw [nsmul_add,hx σ,hy σ,zero_add]
  neg_mem' hx σ := by change (2^k) • (-_)=0; rw [nsmul_neg,hx σ,neg_zero]

lemma actual_power_cocycle_ext (n : F) (hn : n ≠ 0) (k : ℕ)
    {z w : powerValuedCocycles n hn k} (h : ∀ σ : Gal, z.val.val σ=w.val.val σ) : z=w := by
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext σ; exact h σ

end ActualTwoDescentPowerValuedCocycles318
