module
public import SourceLocalProgression318
public section
noncomputable section
namespace ValuativeOrbitBounds318
open ReciprocalGroup318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))

@[expose] def Bound (r : ℤ) (x : F) : Prop := (r:WithTop ℤ)≤v x
@[expose] def Near (r : ℤ) (u w : F) : Prop := Bound v r u ∧ Bound v r (w-1)

lemma weaken {r s : ℤ} {x : F} (h : Bound v s x) (hrs : r≤s) : Bound v r x :=
  le_trans (by exact_mod_cast hrs) h
lemma bzero (r : ℤ) : Bound v r 0 := by simp [Bound]
lemma bone : Bound v 0 (1:F) := by simp [Bound]
lemma badd {r : ℤ} {x y : F} (hx : Bound v r x) (hy : Bound v r y) : Bound v r (x+y) :=
  le_trans (le_min hx hy) (v.map_add x y)
lemma bneg {r : ℤ} {x : F} (hx : Bound v r x) : Bound v r (-x) := by
  simpa only [Bound,v.map_neg] using hx
lemma bsub {r : ℤ} {x y : F} (hx : Bound v r x) (hy : Bound v r y) : Bound v r (x-y) := by
  simpa only [sub_eq_add_neg] using badd v hx (bneg v hy)
lemma bmul {r s : ℤ} {x y : F} (hx : Bound v r x) (hy : Bound v s y) : Bound v (r+s) (x*y) := by
  change ((r+s:ℤ):WithTop ℤ)≤v (x*y)
  rw [v.map_mul]
  exact_mod_cast add_le_add hx hy
lemma bmul_unit {r : ℤ} {x y : F} (hx : Bound v r x) (hy : Bound v 0 y) : Bound v r (x*y) := by
  simpa only [add_zero] using bmul v hx hy
lemma bmul_unit_left {r : ℤ} {x y : F} (hx : Bound v 0 x) (hy : Bound v r y) : Bound v r (x*y) := by
  simpa only [zero_add] using bmul v hx hy
lemma bsquare {r : ℤ} {x : F} (hx : Bound v r x) : Bound v (2*r) (x^2) := by
  simpa only [pow_two,two_mul] using bmul v hx hx
lemma bnat (n : ℕ) : Bound v 0 (n:F) := by
  induction n with
  | zero => exact bzero v 0
  | succ n ih => simpa only [Nat.cast_add,Nat.cast_one] using badd v ih (bone v)
lemma bdiv {r : ℤ} {x y : F} (hx : Bound v r x) (hy : v y=0) : Bound v r (x/y) := by
  simpa only [Bound,v.map_div,hy,sub_zero] using hx
lemma one_near_unit {r : ℤ} {w : F} (hr : 0<r) (hw : Bound v r (w-1)) : v w=0 :=
  NormChainCompleteness.near_one_value v w (lt_of_lt_of_le (by exact_mod_cast hr) hw)

/-- The actual rational group law is additive to second order in all four
near-identity errors. No logarithm, p≥19 hypothesis or square-root choice. -/
theorem addition_errors (D u w a b : F) (r : ℤ) (hr : 1≤r)
    (hD : Bound v 0 D) (hu : Near v r u w) (ha : Near v r a b) :
    Bound v (2*r) (sumU D u w a b-u-a) ∧
      Bound v (2*r) (sumV D u w a b-1-(w-1)-(b-1)) := by
  obtain ⟨hu,hw⟩ := hu
  obtain ⟨ha,hb⟩ := ha
  have hw0 : Bound v 0 w := by rw [Bound,one_near_unit v (by omega) hw]
  have hb0 : Bound v 0 b := by rw [Bound,one_near_unit v (by omega) hb]
  have htwo := bnat v 2
  let T := D*u^2*a^2
  let q := 1+T
  have hT : Bound v (4*r) T := by
    have ht := bmul v (bmul_unit_left v hD (bsquare v hu)) (bsquare v ha)
    simpa only [show 2*r+2*r=4*r by ring] using ht
  have hT2 : Bound v (2*r) T := weaken v hT (by omega)
  have hT0 : Bound v 0 T := weaken v hT (by omega)
  have hqv : v q=0 := one_near_unit v (by omega : 0<4*r) (by simpa only [q,add_sub_cancel_left] using hT)
  have hq : q≠0 := (v.ne_top_iff).mp (by rw [hqv]; simp)
  have hq2 : v (q^2)=0 := by rw [v.map_pow,hqv]; simp
  have hsum : Bound v r (u+a) := badd v hu ha
  have heps : Bound v r ((w-1)+(b-1)) := badd v hw hb
  have huerr : Bound v (2*r) (u*(b-1)+a*(w-1)-(u+a)*T) := by
    apply bsub v
    · exact badd v (by simpa only [two_mul] using bmul v hu hb)
        (by simpa only [two_mul] using bmul v ha hw)
    · exact weaken v (bmul v hsum hT) (by omega)
  have hvb : Bound v 0 (w*b+2) := badd v (bmul_unit v hw0 hb0) htwo
  have hTsq : Bound v (2*r) (T^2) := weaken v (bsquare v hT) (by omega)
  have hquad : Bound v (2*r) (2*D*u*a*(u^2+a^2)) := by
    have hleft := bmul v (bmul_unit_left v (bmul_unit v htwo hD) hu) ha
    have hright := badd v (bsquare v hu) (bsquare v ha)
    exact weaken v (bmul v hleft hright) (by omega)
  have hqerr : Bound v (2*r) (2*T+T^2) :=
    badd v (bmul_unit_left v htwo hT2) hTsq
  have hverr : Bound v (2*r)
      ((w-1)*(b-1)-T*(w*b+2)-T^2-2*D*u*a*(u^2+a^2)-
        ((w-1)+(b-1))*(2*T+T^2)) := by
    apply bsub v
    · apply bsub v
      · apply bsub v
        · exact bsub v (by simpa only [two_mul] using bmul v hw hb) (bmul_unit v hT2 hvb)
        · exact hTsq
      · exact hquad
    · exact weaken v (bmul v heps hqerr) (by omega)
  constructor
  · have he : sumU D u w a b-u-a=(u*(b-1)+a*(w-1)-(u+a)*T)/q := by
      unfold sumU
      dsimp [q,T] at hq ⊢
      field_simp [hq] <;> ring
    rw [he]
    exact bdiv v huerr hqv
  · have he : sumV D u w a b-1-(w-1)-(b-1)=
        ((w-1)*(b-1)-T*(w*b+2)-T^2-2*D*u*a*(u^2+a^2)-
          ((w-1)+(b-1))*(2*T+T^2))/q^2 := by
      unfold sumV
      dsimp [q,T] at hq ⊢
      field_simp [hq] <;> ring
    rw [he]
    exact bdiv v hverr hq2

/-- The same explicit plus-identity chart is closed under the original
addition law, at every positive precision. -/
theorem addition_near (D u w a b : F) (r : ℤ) (hr : 1≤r)
    (hD : Bound v 0 D) (hu : Near v r u w) (ha : Near v r a b) :
    Near v r (sumU D u w a b) (sumV D u w a b) := by
  obtain ⟨heU,heV⟩ := addition_errors v D u w a b r hr hD hu ha
  constructor
  · have he := badd v (badd v (weaken v heU (by omega)) hu.1) ha.1
    convert he using 1 <;> ring
  · have he := badd v (badd v (weaken v heV (by omega)) hu.2) ha.2
    convert he using 1 <;> ring

end ValuativeOrbitBounds318
