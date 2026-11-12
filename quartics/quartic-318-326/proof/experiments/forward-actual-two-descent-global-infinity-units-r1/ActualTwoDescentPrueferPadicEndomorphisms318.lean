module
public import ActualTwoDescentPrimaryPadicAction318
public section
noncomputable section
namespace ActualTwoDescentPrueferPadicEndomorphisms318
set_option maxHeartbeats 16000000
open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentPrueferLevelCoordinates318
open ActualTwoDescentPrimaryPadicScalar318 ActualTwoDescentPrimaryPadicAction318
open ActualTwoDescentPrueferEndResidues318 ActualTwoDescentAdditivePrimaryLevels318
open ActualTwoDescentCyclicEndCoordinates318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance (k : ℕ) : NeZero (2^k) := ⟨pow_ne_zero _ (by decide)⟩

lemma actual_pruefer_add_primary : PrimaryTwo PrueferAdd := fun x => actual_pruefer_is_two_group x.toMul

def padicToPrueferEnd : ℤ_[2] →+* AddMonoid.End PrueferAdd :=
  primaryPadicEndHom actual_pruefer_add_primary

lemma actual_padic_pruefer_end_residue (k : ℕ) (a : ℤ_[2]) :
    prueferEndResidue k (padicToPrueferEnd a)=PadicInt.toZModPow k a := by
  let e := prueferLevelCoordinate k
  let x : PrueferLevel k := e 1
  have hs := actual_primary_padic_scalar_at_level actual_pruefer_add_primary a k x.val x.property
  have hs' : additiveLevelEnd PrueferAdd k (padicToPrueferEnd a) x=
      (PadicInt.toZModPow k a).val • x := Subtype.ext hs
  have he := congrArg e.symm hs'
  change prueferEndResidue k (padicToPrueferEnd a)=e.symm ((PadicInt.toZModPow k a).val • e 1) at he
  simpa only [map_nsmul,e.symm_apply_apply,nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val] using he

lemma actual_pruefer_end_padic_left_inverse (f : AddMonoid.End PrueferAdd) :
    padicToPrueferEnd (prueferEndToPadic f)=f := by
  ext x
  obtain ⟨k,hk⟩ := actual_pruefer_add_primary x
  change primaryPadicScalar actual_pruefer_add_primary (prueferEndToPadic f) x=f x
  rw [actual_primary_padic_scalar_at_level actual_pruefer_add_primary _ k x hk,
    actual_pruefer_end_to_padic_residue]
  exact (actual_pruefer_end_scalar k f x hk).symm

lemma actual_pruefer_end_padic_right_inverse (a : ℤ_[2]) :
    prueferEndToPadic (padicToPrueferEnd a)=a := by
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  rw [actual_pruefer_end_to_padic_residue,actual_padic_pruefer_end_residue]

/-- The ACTUAL endomorphism ring of the literal dyadic subgroup of Q/Z is
native Z_2. Both inverse maps are proved on actual elements and residues. -/
def prueferEndPadicEquiv : AddMonoid.End PrueferAdd ≃+* ℤ_[2] where
  toFun := prueferEndToPadic
  invFun := padicToPrueferEnd
  left_inv := actual_pruefer_end_padic_left_inverse
  right_inv := actual_pruefer_end_padic_right_inverse
  map_mul' := prueferEndToPadic.map_mul
  map_add' := prueferEndToPadic.map_add

end ActualTwoDescentPrueferPadicEndomorphisms318
