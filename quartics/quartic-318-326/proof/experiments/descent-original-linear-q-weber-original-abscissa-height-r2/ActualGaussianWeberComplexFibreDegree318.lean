module
public import ActualGaussianWeberComplexFibreSeed318
public import ActualGaussianWeberRationalDerivativeCap318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Separable
public section
noncomputable section

namespace ActualGaussianWeberComplexFibreDegree318

open Polynomial ActualGaussianWeberComplexFibreSeed318
open ActualGaussianWeberRationalDerivativeCap318

variable {K : Type*} [Field K] [Algebra K ℂ] [DecidableEq ℂ]

/-- For the fixed transcendental target c, the complex inverse-fibre
polynomial of the same original coprime ratio has exactly its full
max degree in *distinct* roots. The derivative cross remains a polynomial
over the original K, where the inverse abscissa evaluation is injective. -/
theorem full_distinct_root_card (A B : K[X]) (hAB : IsCoprime A B) (hB : B ≠ 0)
    (c : ℂ) (hc : Transcendental K c) :
    (((A.map (algebraMap K ℂ)) - C c * (B.map (algebraMap K ℂ))).roots.toFinset).card =
      max A.natDegree B.natDegree := by
  classical
  let f := algebraMap K ℂ
  let N := max A.natDegree B.natDegree
  let P := A.map f - C c * B.map f
  change P.roots.toFinset.card = N
  have hAdeg : (A.map f).natDegree = A.natDegree :=
    natDegree_map_eq_of_injective f.injective A
  have hBdeg : (B.map f).natDegree = B.natDegree :=
    natDegree_map_eq_of_injective f.injective B
  have hProd : (C c * B.map f).natDegree ≤ N := by
    calc
      _ ≤ (C c).natDegree + (B.map f).natDegree := natDegree_mul_le _ _
      _ = B.natDegree := by rw [natDegree_C,hBdeg,zero_add]
      _ ≤ N := le_max_right _ _
  have hLe : P.natDegree ≤ N :=
    (natDegree_sub_le _ _).trans (max_le (hAdeg.trans_le (le_max_left _ _)) hProd)
  by_cases hn : N = 0
  · have hCard := (Multiset.toFinset_card_le P.roots).trans (Polynomial.card_roots' P)
    exact le_antisymm (hCard.trans hLe) (by rw [hn]; exact Nat.zero_le _)
  have hTop : P.coeff N ≠ 0 := by
    intro hh
    have he : f (A.coeff N) = c * f (B.coeff N) := sub_eq_zero.mp
      (by simpa only [P,coeff_sub,coeff_C_mul,coeff_map] using hh)
    by_cases hb : B.coeff N = 0
    · have hlB : B.natDegree < N := by
        apply lt_of_le_of_ne (le_max_right _ _)
        intro e
        exact (leadingCoeff_ne_zero.mpr hB) (by rw [leadingCoeff,e,hb])
      have hN : A.natDegree = N := by
        by_contra neq
        exact (lt_irrefl N) (max_lt_iff.mpr ⟨lt_of_le_of_ne (le_max_left _ _) neq,hlB⟩)
      have hA : A ≠ 0 := by
        intro hA0
        rw [hA0,natDegree_zero] at hN
        exact hn hN.symm
      have hAz : A.coeff N = 0 := by
        apply f.injective
        rw [map_zero]
        simpa only [hb,map_zero,mul_zero] using he
      exact (leadingCoeff_ne_zero.mpr hA) (by rw [leadingCoeff,hN,hAz])
    · have hfb : f (B.coeff N) ≠ 0 := fun h =>
        hb (f.injective (h.trans (map_zero f).symm))
      have hEq : c = f (A.coeff N / B.coeff N) := by
        rw [map_div₀]
        exact (eq_div_iff hfb).mpr he.symm
      apply hc
      rw [hEq]
      exact isAlgebraic_algebraMap _
  have hDeg : P.natDegree = N := le_antisymm hLe (le_natDegree_of_ne_zero hTop)
  letI : CharZero K := ⟨by
    intro m n h
    apply Nat.cast_injective (R := ℂ)
    simpa only [map_natCast] using congrArg f h⟩
  let D := A.derivative * B - A * B.derivative
  have hD : D ≠ 0 := by
    intro e
    have he : A.derivative * B = A * B.derivative := sub_eq_zero.mp e
    obtain ⟨hA,hB'⟩ := derivative_zero_of_coprime_cross hAB he
    apply hn
    change max A.natDegree B.natDegree = 0
    rw [Polynomial.derivative_eq_zero.mp hA,Polynomial.derivative_eq_zero.mp hB']
  have hSep : P.Separable := by
    rw [separable_def,Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ]
    intro x
    simp only [coe_aeval_eq_eval]
    by_cases h : P.eval x = 0
    · right
      intro h'
      have hE : A.eval₂ f x = c * B.eval₂ f x := sub_eq_zero.mp
        (by simpa only [P,eval_sub,eval_mul,eval_C,eval_map] using h)
      have hd : A.derivative.eval₂ f x = c * B.derivative.eval₂ f x := sub_eq_zero.mp
        (by simpa only [P,derivative_sub,derivative_mul,derivative_C,zero_mul,zero_add,
          derivative_map,eval_sub,eval_mul,eval_C,eval_map] using h')
      obtain ⟨_,hinj⟩ := fibre_root_transcendental A B hAB hc hE
      let E := eval₂RingHom f x
      have hEv : E D = 0 := by
        change E (A.derivative * B - A * B.derivative) = 0
        simp only [map_sub,map_mul,coe_eval₂RingHom]
        rw [hd,hE]
        ring
      exact hD (hinj (hEv.trans (map_zero E).symm))
    · exact Or.inl h
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hSep),IsAlgClosed.card_roots_eq_natDegree,hDeg]

end ActualGaussianWeberComplexFibreDegree318
