module
public import Mathlib.RingTheory.ZMod.LocalRing
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Tactic
public section
noncomputable section
namespace ResidueProjectiveSlopes318

/-- Over a local base, use slope y/x on x-unit columns; otherwise the
reciprocal slope x/y is a nonunit. We only need the injection direction,
not a transitivity or lifting assertion from the finite residue ring. -/
abbrev Charts (A : Type*) [CommRing A] := A ⊕ {a : A // ¬IsUnit a}

def code {A : Type*} [CommRing A] (x y : A) (h : IsUnit x ∨ IsUnit y) : Charts A := by
  classical
  exact if hx : IsUnit x then Sum.inl (y*↑(hx.unit⁻¹)) else
    let hy := h.resolve_left hx
    Sum.inr ⟨x*↑(hy.unit⁻¹),fun hu => hx (isUnit_of_mul_isUnit_left hu)⟩

theorem cross {A : Type*} [CommRing A] {x y z w : A}
    (h : IsUnit x ∨ IsUnit y) (k : IsUnit z ∨ IsUnit w)
    (hc : code x y h = code z w k) : x*w-y*z=0 := by
  classical
  by_cases hx : IsUnit x <;> by_cases hz : IsUnit z
  · have he : y*↑(hx.unit⁻¹)=w*↑(hz.unit⁻¹) := by simpa [code,hx,hz] using hc
    have hh := congrArg (fun a : A => a*x*z) he
    have sx : (↑(hx.unit⁻¹):A)*x=1 := by simpa only [hx.unit_spec] using hx.unit.inv_mul
    have sz : (↑(hz.unit⁻¹):A)*z=1 := by simpa only [hz.unit_spec] using hz.unit.inv_mul
    linear_combination -hh + y*z*(sx) - w*x*(sz)
  · simp [code,hx,hz] at hc
  · simp [code,hx,hz] at hc
  · let hy := h.resolve_left hx
    let hw := k.resolve_left hz
    have he : x*↑(hy.unit⁻¹)=z*↑(hw.unit⁻¹) := by simpa [code,hx,hz,hy,hw] using hc
    have hh := congrArg (fun a : A => a*y*w) he
    have sy : (↑(hy.unit⁻¹):A)*y=1 := by simpa only [hy.unit_spec] using hy.unit.inv_mul
    have sw : (↑(hw.unit⁻¹):A)*w=1 := by simpa only [hw.unit_spec] using hw.unit.inv_mul
    linear_combination hh - x*w*sy + z*y*sw

/-- A nonunit residue modulo p^e has representative divisible by p, so its
representative divided by p injects into [0,p^(e−1)). -/
theorem charts_card_le (p e : ℕ) (hp : p.Prime) (he : 0<e) :
    Nat.card (Charts (ZMod (p^e))) ≤ p^e+p^(e-1) := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  letI : NeZero (p^(n+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let A := ZMod (p^(n+1))
  let v : {x : A // ¬IsUnit x} → Fin (p^n) := fun x =>
    ⟨x.val.val/p,(Nat.div_lt_iff_lt_mul hp.pos).mpr <| by simpa [pow_succ] using x.val.val_lt⟩
  have dvd' (x : {x : A // ¬IsUnit x}) : p∣x.val.val := by
    by_contra h
    have hU := (ZMod.isUnit_natCast_iff_not_dvd_pow (d:=n+1) hp (by omega)).mpr h
    exact x.property (by simpa [A] using hU)
  have hj : Function.Injective v := by
    intro x y hh
    have hd : x.val.val/p=y.val.val/p := congrArg Fin.val hh
    apply Subtype.ext
    have hv := congrArg (fun z : ℕ => z*p) hd
    rw [Nat.div_mul_cancel (dvd' x),Nat.div_mul_cancel (dvd' y)] at hv
    exact ZMod.val_injective _ hv
  have hle := Nat.card_le_card_of_injective v hj
  simp only [Nat.card_fin] at hle
  rw [show Nat.card (Charts (ZMod (p^(n+1)))) =
      Nat.card A + Nat.card {x : A // ¬IsUnit x} from Nat.card_sum]
  simpa [A,Nat.card_zmod] using Nat.add_le_add_left hle (p^(n+1))
end ResidueProjectiveSlopes318
