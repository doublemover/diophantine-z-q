module
public import OriginalCasselsGoodCharacterCount318
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section

namespace CTGoodOddReverseResidueLabel318

open scoped BigOperators
open OriginalCasselsGoodCharacterCount318

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Same actual denominator-cleared forward x-fibre, now used at the
reverse coefficients. A nonzero square discriminant in the zero
fibre forces a nonsquare target abscissa carrying an ordinate. -/
theorem exists_nonsquare_label_of_zero_fiber (a b : K) (hb : b≠0)
    (h2 : (2:K)≠0) (hF : ringChar K≠2)
    (hD : discriminant a b 0≠0) (hDsq : IsSquare (discriminant a b 0)) :
    ∃ u : K, ¬IsSquare u ∧ IsSquare (target a b u) := by
  classical
  let S := {x : K | x≠0}
  let f : S → K := fun x => xMap a b x.val
  let chi := quadraticChar K
  have hCard (u : K) : (Fintype.card {x : S // f x=u}:ℤ)=chi (discriminant a b u)+1 := by
    have hc := Fintype.card_congr (fibreRoots a b u h2 hb)
    change Fintype.card {x : S // f x=u}=Fintype.card {r : K // r^2=discriminant a b u} at hc
    let T : Set K := {r : K | r^2=discriminant a b u}
    calc
      _ = (Fintype.card T:ℤ) := congrArg (fun n : ℕ => (n:ℤ)) hc
      _ = (T.toFinset.card:ℤ) := congrArg (fun n : ℕ => (n:ℤ)) (Set.toFinset_card T).symm
      _ = _ := quadraticChar_card_sqrts hF _
  have hSum : (∑ u : K, (chi (discriminant a b u)+1))=(Fintype.card S:ℤ) := by
    calc
      _ = ∑ u : K, ∑ _ : {x : S // f x=u}, (1:ℤ) := by
        apply Finset.sum_congr rfl
        intro u _
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hCard]
      _ = ∑ _ : S, (1:ℤ) := Fintype.sum_fiberwise' f (fun _ => (1:ℤ))
      _ = _ := by simp
  have hSmall : Fintype.card S < Fintype.card K :=
    Fintype.card_lt_of_injective_of_notMem (fun x : S => x.val)
      Subtype.coe_injective (b:=0) (by rintro ⟨x,hx⟩; exact x.prop hx)
  have hSmall' : (Fintype.card S:ℤ) < (Fintype.card K:ℤ) := by exact_mod_cast hSmall
  have hDneg : (∑ u : K, chi (discriminant a b u))<0 := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one] at hSum
    omega
  have hChi : (∑ u : K, chi u)=0 := quadraticChar_sum_zero hF
  by_contra hNone
  have hlower : ∀ u : K, 0 ≤ chi (discriminant a b u)+chi u := by
    intro u
    by_cases hu : u=0
    · subst u
      have hd : chi (discriminant a b 0)=1 := (quadraticChar_one_iff_isSquare hD).mpr hDsq
      rw [hd,show chi (0:K)=0 from (quadraticChar K).map_zero]
      omega
    by_cases hs : IsSquare u
    · rw [show chi u=1 from (quadraticChar_one_iff_isSquare hu).mpr hs]
      by_cases hz : discriminant a b u=0
      · rw [hz,show chi (0:K)=0 from (quadraticChar K).map_zero]
        omega
      · rcases quadraticChar_dichotomy hz with hz | hz <;> rw [show chi (discriminant a b u)=_ from hz] <;> omega
    · have hnS : ¬IsSquare (target a b u) := fun h => hNone ⟨u,hs,h⟩
      have hχ : chi u= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hs
      have hC : chi (target a b u)= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hnS
      change chi (u*discriminant a b u)= -1 at hC
      rw [map_mul,hχ,neg_one_mul] at hC
      rw [hχ]
      omega
  have hnon : 0 ≤ ∑ u : K, (chi (discriminant a b u)+chi u) :=
    Finset.sum_nonneg (fun u _ => hlower u)
  rw [Finset.sum_add_distrib,hChi,add_zero] at hnon
  exact (not_lt_of_ge hnon hDneg)

/-- The reverse target is the actual source after x↦x/4 and y↦y/8,
rather than a separate finite-field isogeny or a new chosen curve. -/
theorem finite_original_nonsquare_abscissa (n : K) (hn : n≠0)
    (h2 : (2:K)≠0) (h3 : (3:K)≠0) (hF : ringChar K≠2) (hD : IsSquare (-3:K)) :
    ∃ x y : K, x≠0 ∧ ¬IsSquare x ∧ y^2=x*(x-n)*(x+3*n) := by
  have h4 : (4:K)≠0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  have h8 : (8:K)≠0 := by convert pow_ne_zero 3 h2 using 1 <;> ring
  have hb : (16:K)*n^2≠0 := by
    have h16 : (16:K)≠0 := by convert pow_ne_zero 4 h2 using 1 <;> ring
    exact mul_ne_zero h16 (pow_ne_zero 2 hn)
  have hDisc : discriminant (-4*n) (16*n^2) 0=(4*n)^2*(-3) := by
    dsimp only [discriminant]
    ring
  have hDisc0 : discriminant (-4*n) (16*n^2) 0≠0 := by
    rw [hDisc]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero h4 hn)) (neg_ne_zero.mpr h3)
  have hDiscS : IsSquare (discriminant (-4*n) (16*n^2) 0) := by
    obtain ⟨r,hr⟩ := hD
    refine ⟨(4*n)*r,?_⟩
    rw [hDisc,hr]
    ring
  obtain ⟨u,hu,⟨t,ht⟩⟩ := exists_nonsquare_label_of_zero_fiber (-4*n) (16*n^2)
    hb h2 hF hDisc0 hDiscS
  have hu0 : u≠0 := by
    intro h
    apply hu
    exact ⟨0,by rw [h,mul_zero]⟩
  refine ⟨u/4,t/8,div_ne_zero hu0 h4,?_,?_⟩
  · rintro ⟨s,hs⟩
    apply hu
    refine ⟨2*s,?_⟩
    calc
      u = 4*(u/4) := by field_simp [h4] <;> ring
      _ = _ := by rw [hs]; ring
  · have ht' : t^2=u*((u-(-4*n))^2-4*(16*n^2)) := by
      change u*((u-(-4*n))^2-4*(16*n^2))=t*t at ht
      simpa only [pow_two] using ht.symm
    calc
      (t/8)^2=t^2/8^2 := div_pow t 8 2
      _=(u/4)*(u/4-n)*(u/4+3*n) := by rw [ht']; field_simp [h4,h8] <;> ring

end CTGoodOddReverseResidueLabel318

#print axioms CTGoodOddReverseResidueLabel318.finite_original_nonsquare_abscissa
