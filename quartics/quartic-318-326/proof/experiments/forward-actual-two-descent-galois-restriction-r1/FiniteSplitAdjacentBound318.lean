module
public import FiniteAdjacentNormLocus318
public section
noncomputable section
namespace FiniteSplitAdjacentBound318
open FiniteAdjacentNormLocus318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def lineCoeff (r : F) (s : Bool) : F := if s then r else -r
@[expose] def lineTag (r x y : F) : Bool := decide (x=r*y)

lemma root_ne (r : F) (hr : r^2= -1) : r≠0 := by
  intro hz
  rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hr
  exact (neg_ne_zero.mpr one_ne_zero) hr.symm

lemma lineCoeff_ne (r : F) (hr : r^2= -1) (s : Bool) : lineCoeff r s≠0 := by
  cases s <;> simp [lineCoeff,root_ne r hr]

/-- Choose one of the two actual split norm-zero lines, including their intersection. -/
lemma line_equation (r : F) (hr : r^2= -1) (x y : F) (hxy : x^2+y^2=0) :
    x=lineCoeff r (lineTag r x y)*y := by
  by_cases he : x=r*y
  · simpa [lineCoeff,lineTag,he] using he
  · have hp : (x-r*y)*(x+r*y)=0 := by
      calc
        _ = x^2-r^2*y^2 := by ring
        _ = x^2+y^2 := by rw [hr]; ring
        _ = 0 := hxy
    have hn : x-r*y≠0 := by simpa only [sub_ne_zero] using he
    have hz := (mul_eq_zero.mp hp).resolve_left hn
    have hx : x= -(r*y) := by linear_combination hz
    simpa [lineCoeff,lineTag,he] using hx

@[expose] def a {κ ε η : F} (z : Bad κ ε η) := z.1.1.1.1
@[expose] def b {κ ε η : F} (z : Bad κ ε η) := z.1.1.1.2
@[expose] def c {κ ε η : F} (z : Bad κ ε η) := z.1.1.2.1.1
@[expose] def d {κ ε η : F} (z : Bad κ ε η) := z.1.1.2.1.2
@[expose] def w {κ ε η : F} (z : Bad κ ε η) := z.1.1.2.2

@[expose] def encode (r κ ε η : F) (z : Bad κ ε η) : Bool×Bool×F×F :=
  (lineTag r (a z+ε) (b z),lineTag r (c z+η) (d z),a z,w z)

/-- Two line choices and the two free original coordinates(a,w) determine
all five coordinates. No estimate on a related quadric is substituted. -/
theorem encode_injective (h2 : (2:F)≠0) (r κ ε η : F) (hr : r^2= -1)
    (hε : ε^2=1) (hη : η^2=1) : Function.Injective (encode r κ ε η) := by
  intro z t he
  have htag1 := congrArg (fun v : Bool×Bool×F×F => v.1) he
  have htag2 := congrArg (fun v : Bool×Bool×F×F => v.2.1) he
  have ha : a z=a t := congrArg (fun v : Bool×Bool×F×F => v.2.2.1) he
  have hw : w z=w t := congrArg (fun v : Bool×Bool×F×F => v.2.2.2) he
  change lineTag r (a z+ε) (b z)=lineTag r (a t+ε) (b t) at htag1
  change lineTag r (c z+η) (d z)=lineTag r (c t+η) (d t) at htag2
  have hη0 : η≠0 := by intro hz; rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hη; exact zero_ne_one hη
  have hlinz := affine_relation κ ε η hε hη z
  have hlint := affine_relation κ ε η hε hη t
  change -2*ε*a z+2*η*c z=κ*(w z)^2 at hlinz
  change -2*ε*a t+2*η*c t=κ*(w t)^2 at hlint
  rw [ha,hw] at hlinz
  have hc : c z=c t := by
    have hp : (2*η)*(c z-c t)=0 := by linear_combination hlinz-hlint
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (mul_ne_zero h2 hη0))
  have hGz := line_equation r hr (a z+ε) (b z) z.2.1
  have hGt := line_equation r hr (a t+ε) (b t) t.2.1
  rw [htag1,ha] at hGz
  have hb : b z=b t := by
    have hp : lineCoeff r (lineTag r (a t+ε) (b t))*(b z-b t)=0 := by
      linear_combination hGt-hGz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (lineCoeff_ne r hr _))
  have hHz := line_equation r hr (c z+η) (d z) z.2.2
  have hHt := line_equation r hr (c t+η) (d t) t.2.2
  rw [htag2,hc] at hHz
  have hd : d z=d t := by
    have hp : lineCoeff r (lineTag r (c t+η) (d t))*(d z-d t)=0 := by
      linear_combination hHt-hHz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (lineCoeff_ne r hr _))
  apply Subtype.ext
  apply Subtype.ext
  change ((a z,b z),(c z,d z),w z)=((a t,b t),(c t,d t),w t)
  rw [ha,hb,hc,hd,hw]

theorem split_card_bound (h2 : (2:F)≠0) (r κ ε η : F) (hr : r^2= -1)
    (hε : ε^2=1) (hη : η^2=1) : Nat.card (Bad κ ε η)≤4*Fintype.card F^2 := by
  classical
  calc
    Nat.card (Bad κ ε η)=Fintype.card (Bad κ ε η) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Bool×Bool×F×F) :=
      Fintype.card_le_of_injective (encode r κ ε η) (encode_injective h2 r κ ε η hr hε hη)
    _ = 4*Fintype.card F^2 := by simp only [Fintype.card_prod,Fintype.card_bool]; ring

/-- Both split and inert forbidden-locus bounds on the literal quadric. -/
theorem adjacent_card_bound (h2 : (2:F)≠0) (κ ε η : F) (hκ : κ≠0)
    (hε : ε^2=1) (hη : η^2=1) : Nat.card (Bad κ ε η)≤4*Fintype.card F^2 := by
  rcases quadraticChar_dichotomy (show (-1:F)≠0 from neg_ne_zero.mpr one_ne_zero) with hs|hi
  · obtain ⟨r,hr⟩ := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mp hs
    exact split_card_bound h2 r κ ε η (by simpa only [pow_two] using hr.symm) hε hη
  · rw [inert_card κ ε η hκ hε hη hi]
    have hcard := Fintype.one_lt_card (α:=F)
    nlinarith

end FiniteSplitAdjacentBound318
