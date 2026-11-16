module
public import OriginalPrimeWeightedSieve318
public section
noncomputable section
namespace LiteralDualLineIncidence318
open TernaryQuadraticLineCover318
set_option maxHeartbeats 2000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def pairing {R : Type*} [CommRing R] (v u : Vector R) : R := v.1*u.1+v.2.1*u.2.1+v.2.2*u.2.2
@[expose] def generator {R : Type*} [CommRing R] (κ : R) (t : Option R) : Vector R :=
  match t with | none => (0,1,0) | some s => (1,κ*s^2,s)
@[expose] def Direction {R : Type*} [CommRing R] (κ : R) (v : Vector R) :=
  {t : Option R // pairing v (generator κ t)=0}
@[expose] def Roots (A B C : F) := {t : F // A+B*t^2+C*t=0}

/-- Actual quadratic-root bound, by factoring about one actual root. No
supplied root-count or generic-position assumption is used. -/
theorem roots_card (A B C : F) (hB : B≠0) : Nat.card (Roots A B C)≤2 := by
  classical
  by_cases hex : ∃ r : F, A+B*r^2+C*r=0
  · obtain ⟨r,hr⟩ := hex
    have other_unique (x y : Roots A B C) (hx : x.1≠r) (hy : y.1≠r) : x=y := by
      have hfactor (z : Roots A B C) : (z.1-r)*(B*(z.1+r)+C)=0 := by
        linear_combination z.2-hr
      have hxx := (mul_eq_zero.mp (hfactor x)).resolve_left (sub_ne_zero.mpr hx)
      have hyy := (mul_eq_zero.mp (hfactor y)).resolve_left (sub_ne_zero.mpr hy)
      apply Subtype.ext
      apply mul_left_cancel₀ hB
      linear_combination hxx-hyy
    let enc : Roots A B C → Bool := fun z => if z.1=r then false else true
    have hinj : Function.Injective enc := by
      intro x y he
      by_cases hx : x.1=r
      · by_cases hy : y.1=r
        · exact Subtype.ext (hx.trans hy.symm)
        · simp [enc,hx,hy] at he
      · by_cases hy : y.1=r
        · simp [enc,hx,hy] at he
        · exact other_unique x y hx hy
    simpa using Nat.card_le_card_of_injective enc hinj
  · letI : IsEmpty (Roots A B C) := ⟨fun z => hex ⟨z.1,z.2⟩⟩
    simp

/-- A nonzero dual vector meets at most TWO literal conic directions.
Infinity is included, not silently discarded from the quadratic count. -/
theorem direction_card_nonzero (κ : F) (hκ : κ≠0) (v : Vector F) (hv : v≠0) :
    Nat.card (Direction κ v)≤2 := by
  classical
  by_cases hz : v.2.1=0
  · have finite_unique (a b : F)
        (ha : pairing v (generator κ (some a))=0)
        (hb : pairing v (generator κ (some b))=0) : a=b := by
      dsimp [pairing,generator] at ha hb
      rw [hz] at ha hb
      by_cases hw : v.2.2=0
      · have hx : v.1=0 := by simpa only [hz,hw,mul_zero,zero_mul,add_zero,mul_one] using ha
        exact False.elim (hv (Prod.ext hx (Prod.ext hz hw)))
      · apply mul_left_cancel₀ hw
        linear_combination ha-hb
    let enc : Direction κ v → Bool := fun z => z.1.isSome
    have hinj : Function.Injective enc := by
      rintro ⟨a,ha⟩ ⟨b,hb⟩ he
      apply Subtype.ext
      cases a with
      | none => cases b <;> simp_all [enc]
      | some a =>
        cases b with
        | none => simp [enc] at he
        | some b => exact congrArg some (finite_unique a b ha hb)
    simpa using Nat.card_le_card_of_injective enc hinj
  · let enc : Direction κ v → Roots v.1 (v.2.1*κ) v.2.2 := fun z =>
      ⟨z.1.getD 0,by
        have hh := z.2
        cases he : z.1 with
        | none =>
          rw [he] at hh
          have hb : v.2.1=0 := by simpa [pairing,generator] using hh
          exact False.elim (hz hb)
        | some a =>
          rw [he] at hh
          simp only [he,Option.getD_some]
          dsimp [pairing,generator] at hh
          linear_combination hh⟩
    have hinj : Function.Injective enc := by
      intro x y he
      have hh := congrArg Subtype.val he
      apply Subtype.ext
      cases hx : x.1 with
      | none =>
        have he0 := x.2
        rw [hx] at he0
        exact False.elim (hz (by simpa [pairing,generator] using he0))
      | some a =>
        cases hy : y.1 with
        | none =>
          have he0 := y.2
          rw [hy] at he0
          exact False.elim (hz (by simpa [pairing,generator] using he0))
        | some b =>
          have hab : a=b := by simpa [enc,hx,hy] using hh
          exact congrArg some hab
    exact (Nat.card_le_card_of_injective enc hinj).trans (roots_card _ _ _ (mul_ne_zero hz hκ))

/-- Zero reduction is the full p+1 exception, counted explicitly. -/
theorem direction_card_zero (κ : F) : Nat.card (Direction κ (0:Vector F))=Fintype.card F+1 := by
  classical
  let e : Direction κ (0:Vector F) ≃ Option F := {
    toFun := Subtype.val
    invFun := fun t => ⟨t,by simp [pairing]⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

end LiteralDualLineIncidence318
