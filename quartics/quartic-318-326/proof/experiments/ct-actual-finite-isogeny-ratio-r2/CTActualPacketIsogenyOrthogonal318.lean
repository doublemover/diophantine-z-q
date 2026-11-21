module
public import CTActualRetainedScalarPair318
public import CTOddSelectedTorsionBasis318
public import CTDyadicActualSourceClasses318
public import OriginalCasselsRealLocalCokernel318
public import OriginalCasselsTernaryLocalCokernel318
public import OriginalCasselsRamifiedClasses318
import CTOriginalPadicValuationPairs318
import all CTActualFiniteIsogenyLinear318
import all CTActualGloballyFiniteIsogenySelmer318
import all CTActualDualConnecting318
import all CTActualRetainedScalarPair318
import all CTDyadicActualSourceClasses318
import all ActualTwoDescentEllipticModel318
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTActualPacketIsogenyOrthogonal318

open CTActualRetainedScalarPair318 CTActualFiniteIsogenyLinear318
open CTActualGloballyFiniteIsogenySelmer318 CTActualDualConnecting318
open CTExplicitLocalBitForms318 CTNativeRealSquareclassEquiv318
open CTNativeDyadicSquareclassCoordinates318 CTDyadicActualSourceClasses318
open CTOddSelectedTorsionBasis318 CTOddSquareclassBasis318
open CTRetainedDyadicTorsionClasses318 CTDyadicSourceTorsionImage318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentEllipticModel318
open OriginalSelectedCasselsParity318 OriginalCasselsDyadicXClass318
open OriginalCasselsNaturalPrimeValuation318 OriginalCasselsRamifiedRootCriterion318
open OriginalCasselsRealLocalCokernel318 OriginalCasselsTernaryLocalCokernel318 
open OriginalCasselsDyadicClassUpper318 OriginalCasselsRamifiedClasses318
open LinearMap.BilinForm
open ActualTwoDescentPadicValuationPairs318 ActualTwoDescentLocalValuationTools318

section Common
variable (K : Type) [Field K] [CharZero K] [DecidableEq K]

theorem sourceContainsOne (n : K) (hn : n≠0) : occurs .reverse K n hn 1 := ⟨0,rfl⟩

theorem sourceContainsN (n : K) (hn : n≠0) :
    occurs .reverse K n hn (classOf n hn) := by
  refine ⟨point n n 0 hn (by simp),?_⟩
  simp only [point,reverseValue,dif_neg hn]

theorem sourceContainsNegThree (n : K) (hn : n≠0) :
    occurs .reverse K n hn (classOf (-3:K) (by norm_num)) := by
  refine ⟨point n 0 0 hn (by simp),?_⟩
  simp only [point,reverseValue,dif_pos rfl]
  exact (class_of_eq_iff _ _ _ _).mpr ⟨n,hn,rfl⟩

theorem sourceContainsMul (n : K) (hn : n≠0) (a b : SquareClass K)
    (ha : occurs .reverse K n hn a) (hb : occurs .reverse K n hn b) :
    occurs .reverse K n hn (a*b) :=
  (mem_localPlane K n hn (a*b)).mp
    ((localPlane K .reverse n hn).add_mem
      ((mem_localPlane K n hn a).mpr ha) ((mem_localPlane K n hn b).mpr hb))

/-- A locally trivial forward image and surjective literal reverse image
give complementarity for the actual local bilinear form. -/
theorem orthogonal_of_one_full (n : K) (hn : n≠0) (B : LinearMap.BilinForm F₂ (ScalarBits K))
    (hF : ∀ P : TargetPoint n, targetClass P=1)
    (hR : ∀ c : SquareClass K, occurs .reverse K n hn c) :
    B.orthogonal (localPlane K .forward n hn)=localPlane K .reverse n hn := by
  ext x
  constructor
  · intro _
    exact (mem_localPlane K n hn x.toMul).mpr (hR x.toMul)
  · intro _
    apply mem_orthogonal_iff.mpr
    intro y hy
    obtain ⟨P,hP⟩ := (mem_localPlane K n hn y.toMul).mp hy
    have he : y=0 := Additive.toMul.injective (hP.symm.trans (hF P))
    rw [he,map_zero,LinearMap.zero_apply]

end Common

local instance : DecidableEq ℝ := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem real_complement (n : ℝ) (hn : n≠0) :
    realForm.orthogonal (localPlane ℝ .forward n hn)=localPlane ℝ .reverse n hn := by
  refine orthogonal_of_one_full ℝ n hn realForm (real_target_class_one n hn) (fun c => ?_)
  have hBit : ∀ a : F₂, a=0 ∨ a=1 := by decide
  rcases hBit (coordinates c).toAdd with h|h
  · have h1 : coordinates c=coordinates 1 := Multiplicative.toAdd.injective
        (h.trans (congrArg Multiplicative.toAdd (map_one coordinates)).symm)
    rw [coordinates_injective h1]
    exact sourceContainsOne ℝ n hn
  · have hm : (coordinates (classOf (-3:ℝ) (by norm_num))).toAdd=1 := by
      rw [coordinates_on_value,if_neg (by norm_num : ¬0<(-3:ℝ))]
    have he := coordinates_injective (Multiplicative.toAdd.injective (h.trans hm.symm))
    rw [he]
    exact sourceContainsNegThree ℝ n hn

section Odd
variable {p : ℕ} [Fact p.Prime]

private theorem torsionBasis_full (n : ℚ_[p]) (hn : n≠0)
    (a : ℚ_[p]) (ha : a≠0) (b : ℤ_[p]) (hb : IsUnit b)
    (hA : occurs .reverse ℚ_[p] n hn (classOf a ha))
    (hB : occurs .reverse ℚ_[p] n hn (classOf (b:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hb.ne_zero)))
    (hSur : Function.Surjective (actualBasis a ha b hb)) (c : SquareClass ℚ_[p]) :
    occurs .reverse ℚ_[p] n hn c := by
  obtain ⟨⟨i,j⟩,rfl⟩ := hSur c
  obtain ⟨h0,h1,h2,h3⟩ := basis_values a ha b hb
  cases i <;> cases j
  · rw [h0]
    exact sourceContainsOne ℚ_[p] n hn
  · rwa [h1]
  · rwa [h2]
  · rw [h3,class_of_mul]
    exact sourceContainsMul ℚ_[p] n hn _ _ hA hB

end Odd

theorem ternary_complement (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    (oddForm 3).orthogonal (localPlane ℚ_[3] .forward (n:ℚ_[3]) (Nat.cast_ne_zero.mpr hn.ne'))=
      localPlane ℚ_[3] .reverse (n:ℚ_[3]) (Nat.cast_ne_zero.mpr hn.ne') := by
  let hN : (n:ℚ_[3])≠0 := Nat.cast_ne_zero.mpr hn.ne'
  refine orthogonal_of_one_full ℚ_[3] (n:ℚ_[3]) hN (oddForm 3)
    (ternary_target_class_one n hn hr) (fun c => ?_)
  obtain ⟨hu,hB⟩ := ternary_actual_basis n hr
  refine torsionBasis_full (n:ℚ_[3]) hN (-3) (by norm_num) (n:ℤ_[3]) hu
    (sourceContainsNegThree ℚ_[3] _ hN) ?_ hB.2 c
  simpa only [PadicInt.coe_natCast] using sourceContainsN ℚ_[3] (n:ℚ_[3]) hN

theorem inert_ramified_complement (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) (p : ℕ) [Fact p.Prime] (hm : p∈n.primeFactors) (hSplit : p%3≠1) :
    (oddForm p).orthogonal (localPlane ℚ_[p] .forward (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne'))=
      localPlane ℚ_[p] .reverse (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne') := by
  let hN : (n:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨hp2,hp3⟩ := selected_primeFactors_ne_two_three hn hr hm
  have hp5 := five_le_prime_of_ne_two_three (Fact.out : p.Prime) hp2 hp3
  have hv := selected_ramified_four_n_valuation n p hn hs hp5 hm
  have hNo : ¬ ∃ r : ZMod p, r^2-r+1=0 := mt (root_iff_residue_one p hp5).mp hSplit
  refine orthogonal_of_one_full ℚ_[p] (n:ℚ_[p]) hN (oddForm p)
    (ramified_target_class_one_of_no_root hp2 (n:ℚ_[p]) hN hv hNo) (fun c => ?_)
  obtain ⟨hu,hB⟩ := ramified_inert_actual_basis n hn hs hr hm hSplit
  refine torsionBasis_full (n:ℚ_[p]) hN (n:ℚ_[p]) hN (-3:ℤ_[p]) hu (sourceContainsN ℚ_[p] _ hN) ?_ hB.2 c
  have hCo : ((-3:ℤ_[p]):ℚ_[p])=(-3:ℚ_[p]) := by
    change PadicInt.Coe.ringHom (-(3:ℤ_[p]))= -3
    rw [map_neg,map_ofNat]
  have he := (class_of_eq_iff ((-3:ℤ_[p]):ℚ_[p]) (-3:ℚ_[p])
    (PadicInt.coe_ne_zero.mpr hu.ne_zero) (by norm_num)).mpr
      ⟨1,one_ne_zero,by simpa only [one_pow,mul_one] using hCo⟩
  rw [he]
  exact sourceContainsNegThree ℚ_[p] _ hN

private theorem reverse_same_dyadic_value (n : ℕ) (hn : 0<n) (P : Point (n:ℚ_[2])) :
    reverseValue ℚ_[2] (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne') P=sourceXClass n hn P := by
  cases P <;> rfl

private theorem dyadicBit_of_value (a : ℚ_[2]) (ha : a≠0) :
    (dyadicVector (Additive.ofMul (classOf a ha))).1=(a.valuation:F₂) := by
  rw [dyadicVector_class,dyadic_value_coords]

private theorem bit_zero_iff_even (m : ℤ) : (m:F₂)=0 ↔ m%2=0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  omega

theorem dyadic_reverse_eq_even_plane (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (c : SquareClass ℚ_[2]) :
    occurs .reverse ℚ_[2] (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne') c ↔
      (dyadicVector (Additive.ofMul c)).1=0 := by
  refine QuotientGroup.induction_on c (fun u => ?_)
  have hu : classOf (u:ℚ_[2]) u.ne_zero=QuotientGroup.mk u := by
    change QuotientGroup.mk (Units.mk0 (u:ℚ_[2]) u.ne_zero)=_
    have hh : Units.mk0 (u:ℚ_[2]) u.ne_zero=u := by apply Units.ext; rfl
    rw [hh]
  rw [←hu,dyadicBit_of_value,bit_zero_iff_even]
  have hRan := actual_source_range_eq_torsion n hn hr
  constructor
  · rintro ⟨P,hP⟩
    let hN : (n:ℚ_[2])≠0 := Nat.cast_ne_zero.mpr hn.ne'
    cases P with
    | zero =>
      change 1=classOf (u:ℚ_[2]) u.ne_zero at hP
      rw [←class_of_one] at hP
      simpa only [Padic.valuation_one,Int.zero_emod] using
        CTActualGoodIsogenyImages318.pdClass_parity (u:ℚ_[2]) 1 u.ne_zero one_ne_zero hP.symm
    | some x y w =>
      by_cases hx : x=0
      · simp only [reverseValue,dif_pos hx] at hP
        have hV : (-3:ℚ_[2]).valuation=0 := by
          rw [actual_valuation_neg]
          change ((3:ℕ):ℚ_[2]).valuation=0
          exact actual_prime_unit_valuation 3 (by decide)
        have hv := CTActualGoodIsogenyImages318.pdClass_parity (u:ℚ_[2])
          (-3*(n:ℚ_[2])^2) u.ne_zero (exceptional_scalar_ne ℚ_[2] (n:ℚ_[2]) hN) hP.symm
        rw [Padic.valuation_mul (by norm_num : (-3:ℚ_[2])≠0) (pow_ne_zero 2 hN),
          hV,Padic.valuation_pow,zero_add] at hv
        omega
      simp only [reverseValue,dif_neg hx] at hP
      have hE := (curve_equation (n:ℚ_[2]) x y).mp w.left
      exact (CTActualGoodIsogenyImages318.pdClass_parity
        (u:ℚ_[2]) x u.ne_zero hx hP.symm).trans (actual_source_even_valuation n hn hr x y hx hE)
  · intro h
    obtain ⟨i,hi⟩ := even_valuation_class_is_torsion n hr (u:ℚ_[2]) u.ne_zero h
    have hm : classOf (u:ℚ_[2]) u.ne_zero ∈ Set.range (torsionClass n hr) := ⟨i,hi.symm⟩
    rw [←hRan] at hm
    obtain ⟨P,hP⟩ := hm
    exact ⟨P,(reverse_same_dyadic_value n hn P).trans hP⟩

theorem dyadic_complement (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    dyadicForm.orthogonal (localPlane ℚ_[2] .forward (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne'))=
      localPlane ℚ_[2] .reverse (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne') := by
  let hN : (n:ℚ_[2])≠0 := Nat.cast_ne_zero.mpr hn.ne'
  let g : ScalarBits ℚ_[2] := Additive.ofMul (classOf (5:ℚ_[2]) (by norm_num))
  have hg : g ∈ localPlane ℚ_[2] .forward (n:ℚ_[2]) hN :=
    (mem_localPlane ℚ_[2] (n:ℚ_[2]) hN _).mpr (actual_class_five_witness n hn hr)
  have hG : dyadicVector g=(0,0,1) := dyadic_coords_five
  have hTest (x : ScalarBits ℚ_[2]) : dyadicForm g x=0 ↔ (dyadicVector x).1=0 := by
    rw [dyadicForm_apply,hG,dyadic_symm (0,0,1)]
    exact dyadic_orthogonal_five _
  ext x
  constructor
  · intro h
    exact (mem_localPlane ℚ_[2] (n:ℚ_[2]) hN x.toMul).mpr
      ((dyadic_reverse_eq_even_plane n hn hr x.toMul).mpr
        ((hTest x).mp (mem_orthogonal_iff.mp h g hg)))
  · intro h
    have hx := (dyadic_reverse_eq_even_plane n hn hr x.toMul).mp
      ((mem_localPlane ℚ_[2] (n:ℚ_[2]) hN x.toMul).mp h)
    apply mem_orthogonal_iff.mpr
    intro y hy
    obtain ⟨P,hP⟩ := (mem_localPlane ℚ_[2] (n:ℚ_[2]) hN y.toMul).mp hy
    rcases actual_dyadic_class_upper n hn hr P with hOne|hFive
    · have he : y=0 := Additive.toMul.injective (hP.symm.trans hOne)
      rw [he,map_zero,LinearMap.zero_apply]
    · have he : y=g := Additive.toMul.injective (hP.symm.trans hFive)
      rw [he]
      exact (hTest x).mpr hx

end CTActualPacketIsogenyOrthogonal318

#print axioms CTActualPacketIsogenyOrthogonal318.real_complement
#print axioms CTActualPacketIsogenyOrthogonal318.ternary_complement
#print axioms CTActualPacketIsogenyOrthogonal318.inert_ramified_complement
#print axioms CTActualPacketIsogenyOrthogonal318.dyadic_complement
