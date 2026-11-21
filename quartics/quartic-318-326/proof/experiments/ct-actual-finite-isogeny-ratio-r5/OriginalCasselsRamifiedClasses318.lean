module
public import OriginalCasselsRamifiedResidue318
public import OriginalCasselsOddLocalFinite318
import all OriginalSelectedCasselsParity318
public section

noncomputable section

namespace OriginalCasselsRamifiedClasses318

open OriginalCasselsOddUnitSquare318 OriginalCasselsOddTargetValuation318
open OriginalCasselsRamifiedResidue318 OriginalCasselsOddLocalFinite318
open OriginalSelectedCasselsParity318 OriginalCasselsDyadicXClass318
open ActualTwoDescentSquareClassQuotient318

variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

private theorem unit_roots_same_class (hp2 : p≠2) (Z W : ℤ_[p])
    (hW : IsUnit W) (hZr : (PadicInt.toZMod Z)^2-PadicInt.toZMod Z+1=0)
    (hWr : (PadicInt.toZMod W)^2-PadicInt.toZMod W+1=0) :
    ∃ t : ℚ_[p], t≠0 ∧ (Z:ℚ_[p])=(W:ℚ_[p])*t^2 := by
  have hWr0 : PadicInt.toZMod W≠0 := (hW.map PadicInt.toZMod).ne_zero
  rcases same_or_inverse_root _ _ hZr hWr with h|h
  · exact unit_ratio_square_of_equal_residue hp2 Z W hWr0 h
  · have hM : PadicInt.toZMod (Z*W^2)=PadicInt.toZMod W := by
      rw [map_mul,map_pow]
      linear_combination (PadicInt.toZMod W)*h
    obtain ⟨s,hs,hS⟩ := unit_ratio_square_of_equal_residue hp2 (Z*W^2) W hWr0 hM
    have hWq : (W:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hW.ne_zero
    refine ⟨s/(W:ℚ_[p]),div_ne_zero hs hWq,?_⟩
    simp only [PadicInt.coe_mul,PadicInt.coe_pow] at hS
    calc
      (Z:ℚ_[p]) = ((W:ℚ_[p])*s^2)/(W:ℚ_[p])^2 :=
        (eq_div_iff (pow_ne_zero 2 hWq)).2 hS
      _ = (W:ℚ_[p])*(s/(W:ℚ_[p]))^2 := by rw [div_pow,mul_div_assoc]

private theorem target_equation (n x y : ℚ_[p])
    (H : (targetModel n).toAffine.Nonsingular x y) :
    y^2=x*(x^2-4*n*x+16*n^2) := by
  have h := H.left
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [targetModel,zero_mul,add_zero,zero_add] at h
  linear_combination h

private theorem class_of_square_abscissa (n x y : ℚ_[p]) (hn : n≠0) (hx : x≠0)
    (he : y^2=x*(x^2-4*n*x+16*n^2)) (h : ∃ r : ℚ_[p], r≠0 ∧ x=r^2) :
    targetClass (targetPoint n x y hn he)=1 := by
  rw [target_class_at_affine hn hx he,←class_of_one]
  obtain ⟨r,hr,heR⟩ := h
  exact (class_of_eq_iff _ _ hx one_ne_zero).mpr ⟨r,hr,by simpa only [one_mul] using heR⟩

/-- If there is no residue root, the exact target image is trivial. -/
theorem ramified_target_class_one_of_no_root (hp2 : p≠2) (n : ℚ_[p]) (hn : n≠0)
    (hvn : ((4:ℚ_[p])*n).valuation=1)
    (hN : ¬∃ r : ZMod p, r^2-r+1=0) (P : TargetPoint n) :
    targetClass P=1 := by
  cases P with
  | zero => rfl
  | some x y H =>
    by_cases hx : x=0
    · subst x
      simp [targetClass]
    · have he := target_equation n x y H
      by_cases hvx : x.valuation=1
      · obtain ⟨Z,_,_,hr⟩ := actual_ramified_residue n x y hn hx hvn hvx he
        exact (hN ⟨PadicInt.toZMod Z,hr⟩).elim
      · exact class_of_square_abscissa n x y hn hx he
          (abscissa_square_of_factor_square n x y hx he
            (factor_square_of_unequal_val hp2 n x hn hx (fun h => hvx (h.trans hvn))))

/-- If a residue root exists, the true target image is exactly the pair
of classes represented by infinity and one actual ordinate-zero point.
The nontrivial member is the class of that *actual* abscissa. -/
theorem ramified_actual_two_classes (hp : 5≤p) (hp2 : p≠2) (n : ℚ_[p]) (hn : n≠0)
    (hvn : ((4:ℚ_[p])*n).valuation=1) (r : ZMod p) (hr : r^2-r+1=0) :
    ∃ P₀ : TargetPoint n, targetClass P₀≠1 ∧
      ∀ P : TargetPoint n, targetClass P=1 ∨ targetClass P=targetClass P₀ := by
  obtain ⟨W,hW,hWred,hWe⟩ := lift_ramified_root hp r hr
  let u := (4:ℚ_[p])*n
  have hu : u≠0 := mul_ne_zero (by norm_num) hn
  have huval : u.valuation=1 := hvn
  let x₀ := u*(W:ℚ_[p])
  have hW0 : (W:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hW.ne_zero
  have hx₀ : x₀≠0 := mul_ne_zero hu hW0
  have hwq : (W:ℚ_[p])^2-(W:ℚ_[p])+1=0 := by
    calc
      _ = algebraMap ℤ_[p] ℚ_[p] (W^2-W+1) := by
        rw [map_add,map_sub,map_pow,map_one,PadicInt.algebraMap_apply]
      _ = 0 := by rw [hWe,map_zero]
  have hG : x₀^2-4*n*x₀+16*n^2=0 := by
    calc
      _=u^2*((W:ℚ_[p])^2-(W:ℚ_[p])+1) := by dsimp [x₀,u]; ring
      _=0 := by rw [hwq,mul_zero]
  have hY₀ : (0:ℚ_[p])^2=x₀*(x₀^2-4*n*x₀+16*n^2) := by rw [hG,mul_zero,zero_pow (by decide : (2:ℕ)≠0)]
  let P₀ := targetPoint n x₀ 0 hn hY₀
  have hc₀ : targetClass P₀=classOf x₀ hx₀ := target_class_at_affine hn hx₀ hY₀
  have hx₀v : x₀.valuation=1 := by
    dsimp [x₀]
    rw [Padic.valuation_mul hu hW0,huval,actual_val_zero_of_unit W hW,add_zero]
  refine ⟨P₀,?_,?_⟩
  · intro h1
    rw [hc₀,←class_of_one] at h1
    obtain ⟨v,_,hv⟩ := (class_of_eq_iff _ _ hx₀ one_ne_zero).mp h1
    rw [one_mul] at hv
    have h := congrArg Padic.valuation hv
    rw [hx₀v,Padic.valuation_pow] at h
    omega
  · intro P
    cases P with
    | zero => exact Or.inl rfl
    | some x y H =>
      by_cases hx : x=0
      · subst x
        exact Or.inl (by simp [targetClass])
      · have he := target_equation n x y H
        by_cases hvx : x.valuation=1
        · right
          obtain ⟨Z,_,hX,hZ⟩ := actual_ramified_residue n x y hn hx hvn hvx he
          have hWr : (PadicInt.toZMod W)^2-PadicInt.toZMod W+1=0 := by rwa [hWred]
          obtain ⟨t,ht,htw⟩ := unit_roots_same_class hp2 Z W hW hZ hWr
          change targetClass (targetPoint n x y hn he)=targetClass P₀
          rw [target_class_at_affine hn hx he,hc₀]
          exact (class_of_eq_iff _ _ hx hx₀).mpr ⟨t,ht,by rw [hX,htw]; dsimp [x₀,u]; ring⟩
        · left
          exact class_of_square_abscissa n x y hn hx he
            (abscissa_square_of_factor_square n x y hx he
              (factor_square_of_unequal_val hp2 n x hn hx (fun h => hvx (h.trans hvn))))

end OriginalCasselsRamifiedClasses318

#print axioms OriginalCasselsRamifiedClasses318.ramified_actual_two_classes
