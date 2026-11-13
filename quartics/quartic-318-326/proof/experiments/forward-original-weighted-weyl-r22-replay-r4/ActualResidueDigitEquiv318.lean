module
public import ActualPrimitiveDigitLiftCount318
public section
noncomputable section
namespace ActualResidueDigitEquiv318
set_option maxHeartbeats 16000000

/-- Genuine base-m digit decomposition of ALL residues modulo m*p.
This is a set equivalence, NOT a CRT ring isomorphism: m and p may
share prime factors, as they do at every p-adic lifting step. -/
@[expose] def digitEquiv (m p : ℕ) [NeZero m] [NeZero p] :
    ZMod (m*p) ≃ ZMod m×ZMod p where
  toFun y := ((y.val:ZMod m),(y.val/m:ZMod p))
  invFun z := (z.1.val+m*z.2.val:ℕ)
  left_inv y := by
    have hy : y.val/m<p := (Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr (by
      simpa only [mul_comm] using y.val_lt)
    change (((y.val:ZMod m).val+m*(y.val/m:ZMod p).val:ℕ):ZMod (m*p))=y
    rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hy,Nat.mod_add_div]
    exact ZMod.natCast_zmod_val y
  right_inv z := by
    have hz : z.1.val+m*z.2.val<m*p := by
      have hx := z.1.val_lt
      have ht := z.2.val_lt
      have hm := NeZero.pos m
      nlinarith
    have hv : ((z.1.val+m*z.2.val:ℕ):ZMod (m*p)).val=z.1.val+m*z.2.val :=
      ZMod.val_natCast_of_lt hz
    apply Prod.ext
    · change ((((z.1.val+m*z.2.val:ℕ):ZMod (m*p)).val:ℕ):ZMod m)=z.1
      rw [hv,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero,ZMod.natCast_zmod_val]
    · change (((((z.1.val+m*z.2.val:ℕ):ZMod (m*p)).val)/m:ℕ):ZMod p)=z.2
      rw [hv]
      have he : (z.1.val+m*z.2.val)/m=z.2.val := by
        rw [add_comm,Nat.mul_add_div (NeZero.pos m),Nat.div_eq_of_lt z.1.val_lt,add_zero]
      rw [he,ZMod.natCast_zmod_val]

@[expose] def reduce (m p : ℕ) : ZMod (m*p) →+* ZMod m :=
  ZMod.castHom (dvd_mul_right m p) (ZMod m)

lemma actual_base_component (m p : ℕ) [NeZero m] [NeZero p] (y : ZMod (m*p)) :
    (digitEquiv m p y).1=reduce m p y := by
  change (y.val:ZMod m)=reduce m p y
  have hh := congrArg (reduce m p) (ZMod.natCast_zmod_val y)
  simpa only [map_natCast] using hh

/-- All residues above a fixed ORIGINAL base residue are exactly the
p actual digits. Both maps are the concrete base-m maps above. -/
@[expose] def fiberEquiv (m p : ℕ) [NeZero m] [NeZero p] (x : ZMod m) :
    ZMod p ≃ {y : ZMod (m*p) // reduce m p y=x} where
  toFun h := ⟨(digitEquiv m p).symm (x,h),by
    rw [←actual_base_component,Equiv.apply_symm_apply]⟩
  invFun y := (digitEquiv m p y.1).2
  left_inv h := by
    exact congrArg Prod.snd ((digitEquiv m p).apply_symm_apply (x,h))
  right_inv y := by
    apply Subtype.ext
    apply (digitEquiv m p).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact y.2.symm.trans (actual_base_component m p y.1).symm
    · rfl

end ActualResidueDigitEquiv318
