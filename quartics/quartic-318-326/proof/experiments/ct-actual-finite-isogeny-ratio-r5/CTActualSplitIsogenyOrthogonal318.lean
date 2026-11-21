module
public import CTActualPacketIsogenyOrthogonal318
public import CTRamifiedSplitSourceClasses318
import all CTActualRetainedScalarPair318
import all CTActualDualConnecting318
import all CTActualGloballyFiniteIsogenySelmer318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import all Mathlib.NumberTheory.LegendreSymbol.Basic
public section
noncomputable section

namespace CTActualSplitIsogenyOrthogonal318

open CTActualPacketIsogenyOrthogonal318 CTActualRetainedScalarPair318
open CTActualFiniteIsogenyLinear318 CTActualGloballyFiniteIsogenySelmer318
open CTActualDualConnecting318 CTNativeOddSquareclassCoordinates318 CTExplicitLocalBitForms318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentEllipticModel318
open ActualTwoDescentLocalValuationTools318
open OriginalSelectedCasselsParity318 OriginalCasselsDyadicXClass318
open OriginalCasselsRamifiedResidue318 OriginalCasselsRamifiedClasses318
open OriginalCasselsRamifiedRootCriterion318 CTRamifiedSplitSourceClasses318
open CTOddSelectedTorsionBasis318
open LinearMap.BilinForm

variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

private theorem forward_split_generator (hp : 5≤p) (hp2 : p≠2) (hSplit : p%3=1)
    (n : ℚ_[p]) (hn : n≠0) (hv : n.valuation=1) :
    let A := classOf n hn
    let neg := classOf (-1:ℚ_[p]) (by norm_num)
    (∃ P : TargetPoint n, targetClass P=A*neg) ∧
      ∀ P : TargetPoint n, targetClass P=1 ∨ targetClass P=A*neg := by
  have h4 : (4:ℚ_[p])≠0 := by norm_num
  have h4V : (4:ℚ_[p]).valuation=0 := by
    change ((4:ℕ):ℚ_[p]).valuation=0
    apply actual_prime_unit_valuation
    exact fun hd => (by omega : ¬p≤4) (Nat.le_of_dvd (by decide : 0<4) hd)
  have hV : ((4:ℚ_[p])*n).valuation=1 := by
    rw [Padic.valuation_mul h4 hn,h4V,hv,zero_add]
  obtain ⟨r,hr⟩ := (root_iff_residue_one p hp).mpr hSplit
  obtain ⟨W,hW,_,hWe⟩ := lift_ramified_root hp r hr
  let w : ℚ_[p] := W
  have hw : w≠0 := PadicInt.coe_ne_zero.mpr hW.ne_zero
  have hE : w^2-w+1=0 := by
    have he := congrArg (algebraMap ℤ_[p] ℚ_[p]) hWe
    simpa only [w,map_pow,map_sub,map_add,map_one,map_zero,PadicInt.algebraMap_apply] using he
  let x := 4*n*w
  have hx : x≠0 := mul_ne_zero (mul_ne_zero h4 hn) hw
  have hxV : x.valuation=1 := by
    change ((4*n)*w).valuation=1
    rw [Padic.valuation_mul (mul_ne_zero h4 hn) hw,hV,show w.valuation=0 from actual_val_zero_of_unit W hW,add_zero]
  have hXY : (0:ℚ_[p])^2=x*(x^2-4*n*x+16*n^2) := by
    dsimp [x]
    calc
      _=0 := by ring
      _=(4*n*w)*((4*n)^2*(w^2-w+1)) := by rw [hE,mul_zero,mul_zero]
      _=_ := by ring
  let Q := targetPoint n x 0 hn hXY
  have hc : targetClass Q=classOf x hx := target_class_at_affine hn hx hXY
  have hxK : classOf x hx=classOf n hn*classOf (-1:ℚ_[p]) (by norm_num) := by
    rw [←class_of_mul]
    refine (class_of_eq_iff _ _ _ _).mpr ⟨2*w^2,mul_ne_zero (by norm_num) (pow_ne_zero 2 hw),?_⟩
    have h := ramified_root_neg_square w hE
    calc
      x=4*n*w := rfl
      _=n*(-1)*(2^2*(w^2)^2) := by rw [←h]; ring
      _=_ := by ring
  have hQ : targetClass Q≠1 := by
    intro h
    rw [hc,←class_of_one] at h
    have he := CTActualGoodIsogenyImages318.pdClass_parity x 1 hx one_ne_zero h
    rw [hxV,Padic.valuation_one] at he
    omega
  obtain ⟨Q₀,_,hAll⟩ := ramified_actual_two_classes hp hp2 n hn hV r hr
  have hEq : targetClass Q=targetClass Q₀ :=
    (hAll Q).resolve_left hQ
  refine ⟨⟨Q,hc.trans hxK⟩,fun P => ?_⟩
  rcases hAll P with h|h
  · exact Or.inl h
  · exact Or.inr (h.trans (hEq.symm.trans (hc.trans hxK)))

private theorem reverse_split_generator (hp : 5≤p) (hp2 : p≠2) (hSplit : p%3=1)
    (n : ℚ_[p]) (hn : n≠0) (hv : n.valuation=1) (c : SquareClass ℚ_[p]) :
    occurs .reverse ℚ_[p] n hn c ↔ c=1 ∨ c=classOf n hn := by
  constructor
  · rintro ⟨P,hP⟩
    cases P with
    | zero => exact Or.inl hP.symm
    | some x y h =>
      by_cases hx : x=0
      · simp only [reverseValue,dif_pos hx] at hP
        have he : classOf (-3*n^2) (exceptional_scalar_ne ℚ_[p] n hn)=
            classOf (-3:ℚ_[p]) (by norm_num) :=
          (class_of_eq_iff _ _ _ _).mpr ⟨n,hn,rfl⟩
        exact Or.inl (hP.symm.trans (he.trans (ramified_split_minusThree_class_one hp hp2 hSplit)))
      simp only [reverseValue,dif_neg hx] at hP
      have hC := (curve_equation n x y).mp h.left
      rcases selected_split_ramified_affine_labels hp hp2 n x y hn hv hx hSplit hC with
        ⟨u,hu,hU⟩|⟨u,hu,hU⟩
      · apply Or.inl
        rw [←class_of_one,←hP]
        exact (class_of_eq_iff _ _ _ _).mpr ⟨u,hu,by simpa only [one_mul] using hU⟩
      · apply Or.inr
        rw [←hP]
        exact (class_of_eq_iff _ _ _ _).mpr ⟨u,hu,hU⟩
  · rintro (rfl|rfl)
    · exact sourceContainsOne ℚ_[p] n hn
    · exact sourceContainsN ℚ_[p] n hn

private theorem odd_neg_one_row :
    oddVector p (Additive.ofMul (classOf (-1:ℚ_[p]) (by norm_num)))=(0,oddSign p) := by
  have hu : IsUnit (-1:ℤ_[p]) := (isUnit_one : IsUnit (1:ℤ_[p])).neg
  have hC : classOf ((-1:ℤ_[p]):ℚ_[p]) (PadicInt.coe_ne_zero.mpr hu.ne_zero)=
      classOf (-1:ℚ_[p]) (by norm_num) :=
    (class_of_eq_iff _ _ _ _).mpr
      ⟨1,one_ne_zero,by simp only [PadicInt.coe_neg,PadicInt.coe_one,one_pow,mul_one]⟩
  have hh := odd_coords_of_integral_unit p (-1:ℤ_[p]) hu
  rw [hC,map_neg,map_one] at hh
  rw [oddVector_class,hh]
  congr 1 <;> simp [oddSign,legendreSym]

private theorem actual_oddVector_injective (hp2 : p≠2) : Function.Injective (oddVector p) := by
  intro a b h
  apply Additive.toMul.injective
  apply oddCoordinates_injective p hp2
  apply Multiplicative.toAdd.injective
  exact h

private theorem odd_opposite_bit_table :
    ∀ (k u : F₂) (z : F₂ × F₂),
      odd k (1,u+k) z=0 ↔ z=(0,0) ∨ z=(1,u) := by decide

/-- The two actual ramified split lines are opposite orthogonals.
The target's signed root contributes exactly the [-1] class, so
its unit bit differs from the source's by the actual odd κ. -/
theorem split_ramified_complement (hp : 5≤p) (hp2 : p≠2) (hSplit : p%3=1)
    (n : ℚ_[p]) (hn : n≠0) (hv : n.valuation=1) :
    (oddForm p).orthogonal (localPlane ℚ_[p] .forward n hn)=
      localPlane ℚ_[p] .reverse n hn := by
  let a : ScalarBits ℚ_[p] := Additive.ofMul (classOf n hn)
  let m : ScalarBits ℚ_[p] := Additive.ofMul (classOf (-1:ℚ_[p]) (by norm_num))
  let b := a+m
  let u := (oddVector p a).2
  have ha : oddVector p a=(1,u) := by
    apply Prod.ext
    · change (oddVector p (Additive.ofMul (classOf n hn))).1=1
      rw [oddVector_class,odd_value_coords,hv,Int.cast_one]
    · rfl
  have hb : oddVector p b=(1,u+oddSign p) := by
    change oddVector p (a+m)=_
    rw [map_add,ha,show oddVector p m=(0,oddSign p) from odd_neg_one_row]
    simp
  obtain ⟨hF,hAll⟩ := forward_split_generator hp hp2 hSplit n hn hv
  have hbF : b ∈ localPlane ℚ_[p] .forward n hn :=
    (mem_localPlane ℚ_[p] n hn b.toMul).mpr hF
  have hTest (z : ScalarBits ℚ_[p]) : oddForm p b z=0 ↔ z=0 ∨ z=a := by
    rw [oddForm_apply,hb,odd_opposite_bit_table]
    rw [←show oddVector p 0=((0,0):F₂ × F₂) from map_zero (oddVector p),←ha]
    simp only [(actual_oddVector_injective hp2).eq_iff]
  ext z
  constructor
  · intro hz
    have hz' := (hTest z).mp (mem_orthogonal_iff.mp hz b hbF)
    apply (mem_localPlane ℚ_[p] n hn z.toMul).mpr
    apply (reverse_split_generator hp hp2 hSplit n hn hv _).mpr
    rcases hz' with h|h
    · exact Or.inl (congrArg Additive.toMul h)
    · exact Or.inr (congrArg Additive.toMul h)
  · intro hz
    have hz' := (reverse_split_generator hp hp2 hSplit n hn hv _).mp
      ((mem_localPlane ℚ_[p] n hn z.toMul).mp hz)
    have hZ : z=0 ∨ z=a := hz'.imp Additive.toMul.injective Additive.toMul.injective
    apply mem_orthogonal_iff.mpr
    intro y hy
    obtain ⟨P,hP⟩ := (mem_localPlane ℚ_[p] n hn y.toMul).mp hy
    rcases hAll P with h|h
    · have hy' : y=0 := Additive.toMul.injective (hP.symm.trans h)
      rw [hy',map_zero,LinearMap.zero_apply]
    · have hy' : y=b := Additive.toMul.injective (hP.symm.trans h)
      rw [hy']
      exact (hTest z).mpr hZ

end CTActualSplitIsogenyOrthogonal318

#print axioms CTActualSplitIsogenyOrthogonal318.split_ramified_complement
