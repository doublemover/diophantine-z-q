module
public import ActualTwoDescentPrueferEndResidues318
public section
noncomputable section
namespace ActualTwoDescentPrimaryScalarCongruence318
set_option maxHeartbeats 16000000
variable {A : Type} [AddCommGroup A]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance (k : ℕ) : NeZero (2^k) := ⟨pow_ne_zero _ (by decide)⟩

lemma actual_nsmul_mod_annihilator (m c : ℕ) (x : A) (hx : m • x=0) :
    (c % m) • x=c • x := by
  have h : (c % m+c/m*m) • x=c • x := by rw [Nat.mod_add_div']
  simpa only [add_nsmul,mul_nsmul,hx,nsmul_zero,add_zero] using h

lemma actual_padic_residue_scalar_reduction (a : ℤ_[2]) (i j : ℕ) (h : i ≤ j)
    (x : A) (hx : (2^i) • x=0) :
    (PadicInt.toZModPow j a).val • x=(PadicInt.toZModPow i a).val • x := by
  have hr := PadicInt.cast_toZModPow i j h a
  have hv := congrArg ZMod.val hr
  simp only [ZMod.cast_eq_val,ZMod.val_natCast] at hv
  rw [←actual_nsmul_mod_annihilator (2^i) (PadicInt.toZModPow j a).val x hx,hv]

lemma actual_zmod_residue_add_smul (k : ℕ) (a b : ZMod (2^k))
    (x : A) (hx : (2^k) • x=0) : (a+b).val • x=a.val • x+b.val • x := by
  rw [ZMod.val_add,actual_nsmul_mod_annihilator _ _ x hx,add_nsmul]

lemma actual_zmod_residue_mul_smul (k : ℕ) (a b : ZMod (2^k))
    (x : A) (hx : (2^k) • x=0) : (a*b).val • x=a.val • (b.val • x) := by
  rw [ZMod.val_mul,actual_nsmul_mod_annihilator _ _ x hx,mul_nsmul]

end ActualTwoDescentPrimaryScalarCongruence318
