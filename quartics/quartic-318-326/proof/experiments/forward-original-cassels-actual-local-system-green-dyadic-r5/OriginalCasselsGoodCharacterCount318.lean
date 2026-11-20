module
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public section

noncomputable section

namespace OriginalCasselsGoodCharacterCount318

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev source (a b x : K) : K := x*(x^2+a*x+b)
abbrev discriminant (a b u : K) : K := (u-a)^2-4*b
abbrev target (a b u : K) : K := u*discriminant a b u
abbrev xMap (a b x : K) : K := x+a+b/x

private theorem fibre_iff (a b u x : K) (hx : x≠0) :
    xMap a b x=u ↔ x^2+(a-u)*x+b=0 := by
  constructor
  · intro h
    change x+a+b/x=u at h
    field_simp [hx] at h
    linear_combination h
  · intro h
    change x+a+b/x=u
    field_simp [hx]
    linear_combination h

/-- Completion of the exact denominator-cleared fibre quadratic.
The condition b≠0 excludes x=0 before using its inverse. -/
def fibreRoots (a b u : K) (h2 : (2:K)≠0) (hb : b≠0) :
    {x : {x : K // x≠0} // xMap a b x.val=u} ≃
      {r : K // r^2=discriminant a b u} where
  toFun x := ⟨2*x.val.val+a-u,by
    have h := (fibre_iff a b u x.val.val x.val.prop).mp x.prop
    change (2*x.val.val+a-u)^2=(u-a)^2-4*b
    linear_combination 4*h⟩
  invFun r := by
    let x := (r.val+u-a)/2
    have h4 : (4:K)≠0 := by convert mul_ne_zero h2 h2 using 1 <;> ring
    have hlin : 2*x+a-u=r.val := by dsimp [x]; field_simp [h2] <;> ring
    have hq : (4:K)*(x^2+(a-u)*x+b)=0 := by
      calc
        _ = (2*x+a-u)^2-discriminant a b u := by
          change _=(2*x+a-u)^2-((u-a)^2-4*b)
          ring
        _ = 0 := by rw [hlin,r.prop,sub_self]
    have hh : x^2+(a-u)*x+b=0 := (mul_eq_zero.mp hq).resolve_left h4
    have hx : x≠0 := by
      intro h
      apply hb
      simpa only [h,zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero,zero_add] using hh
    exact ⟨⟨x,hx⟩,(fibre_iff a b u x hx).2 hh⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((2*x.val.val+a-u)+u-a)/2=x.val.val
    field_simp [h2] <;> ring
  right_inv r := by
    apply Subtype.ext
    change 2*((r.val+u-a)/2)+a-u=r.val
    field_simp [h2] <;> ring

/-- Finite character identity for the two actual cubics; neither any
elliptic group law over the residue field nor a Tate module is involved. -/
theorem character_count_identity (a b : K) (hb : b≠0)
    (h2 : (2:K)≠0) (hF : ringChar K≠2) :
    (∑ x : K, quadraticChar K (source a b x)) =
      ∑ u : K, quadraticChar K (target a b u) := by
  classical
  let S := {x : K | x≠0}
  let χ := quadraticChar K
  let f : S → K := fun x => xMap a b x.val
  have hvals : (∑ x : K, χ (source a b x))=∑ x : S, χ (f x) := by
    apply Finset.sum_congr_set S
    · intro x hx
      have hx' : x≠0 := hx
      have he : source a b x=x^2*xMap a b x := by
        change x*(x^2+a*x+b)=x^2*(x+a+b/x)
        field_simp [hx'] <;> ring
      rw [he,map_mul]
      have hχ : χ (x^2)=1 :=
        (quadraticChar_one_iff_isSquare (pow_ne_zero _ hx')).2 ⟨x,by rw [pow_two]⟩
      simp only [hχ,one_mul,f]
    · intro x hx
      have h : x=0 := by by_contra h; exact hx h
      simp only [h,source,zero_mul,map_zero]
  have hcnt (u : K) : (Fintype.card {x : S // f x=u}:ℤ)=χ (discriminant a b u)+1 := by
    have hc := Fintype.card_congr (fibreRoots a b u h2 hb)
    change Fintype.card {x : S // f x=u}=Fintype.card {r : K // r^2=discriminant a b u} at hc
    rw [hc,←Set.toFinset_card]
    exact quadraticChar_card_sqrts hF (discriminant a b u)
  rw [hvals,←Fintype.sum_fiberwise' f (fun u => χ u)]
  calc
    _ = ∑ u : K, (χ (discriminant a b u)+1)*χ u := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcnt]
    _ = (∑ u : K, χ (target a b u)) + ∑ u : K, χ u := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [show target a b u=u*discriminant a b u from rfl,map_mul]
      ring
    _ = _ := by rw [show (∑ u : K,χ u)=0 from quadraticChar_sum_zero hF,add_zero]

abbrev RawPoints (f : K → K) := Option (Σ x : K, {y : K // y^2=f x})

private theorem raw_card (f : K → K) (hF : ringChar K≠2) :
    (Fintype.card (RawPoints f):ℤ) =
      1+(∑ x : K, quadraticChar K (f x)+1) := by
  have row (x : K) : (Fintype.card {y : K // y^2=f x}:ℤ)=quadraticChar K (f x)+1 := by
    rw [←Set.toFinset_card]
    exact quadraticChar_card_sqrts hF (f x)
  rw [Fintype.card_option,Fintype.card_sigma]
  push_cast
  simp_rw [row]
  ring

/-- Same finite number of literal affine labels plus infinity. -/
theorem raw_points_same_card (a b : K) (hb : b≠0) (h2 : (2:K)≠0) (hF : ringChar K≠2) :
    Fintype.card (RawPoints (source a b))=Fintype.card (RawPoints (target a b)) := by
  apply Int.ofNat.inj
  rw [raw_card (source a b) hF,raw_card (target a b) hF]
  simp only [Finset.sum_add_distrib,character_count_identity a b hb h2 hF]

end OriginalCasselsGoodCharacterCount318

#print axioms OriginalCasselsGoodCharacterCount318.character_count_identity
#print axioms OriginalCasselsGoodCharacterCount318.raw_points_same_card
