module
public import CTRealNativeBar318
public import CTComplexUnitNorm318
import all CTRealNativeBar318
import all Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
public section
noncomputable section

namespace CTRealNativeNormClass318

open CTRealClosureConjugation318 CTRealNativeBar318 CTContinuousFieldHTwo318
open CTFieldPrimitiveRestriction318 CTComplexUnitNorm318

local instance : DecidableEq ℝ := Classical.decEq _

/-- Forget the additive notation and transport through the single
ℝ-algebra equivalence chosen for the actual closure. -/
def asComplexUnit (a : A) : ℂˣ :=
  Units.map realClosureEquiv.toRingEquiv.toMonoidHom a.toMul

theorem asComplexUnit_coe (a : A) :
    (asComplexUnit a : ℂ) = realClosureEquiv (a.toMul : Rbar) := rfl

theorem asComplexUnit_injective : Function.Injective asComplexUnit := by
  intro a b h
  have h' : (asComplexUnit a : ℂ) = (asComplexUnit b : ℂ) := congrArg Units.val h
  have he : a.toMul = b.toMul := Units.ext (realClosureEquiv.injective h')
  exact congrArg Additive.ofMul he

theorem asComplexUnit_surjective : Function.Surjective asComplexUnit := by
  intro v
  refine ⟨Additive.ofMul (Units.map realClosureEquiv.symm.toRingEquiv.toMonoidHom v),?_⟩
  apply Units.ext
  change realClosureEquiv (realClosureEquiv.symm (v : ℂ)) = (v : ℂ)
  exact realClosureEquiv.apply_symm_apply _

theorem asComplexUnit_add (a b : A) :
    (asComplexUnit (a+b) : ℂ) = (asComplexUnit a : ℂ) * (asComplexUnit b : ℂ) := by
  change realClosureEquiv ((a.toMul : Rbar) * (b.toMul : Rbar)) = _
  rw [map_mul] <;> rfl

theorem asComplexUnit_conj (a : A) :
    (asComplexUnit (realBarAction realConjugation a) : ℂ) =
      (starRingEnd ℂ) (asComplexUnit a : ℂ) := by
  have h := realAutTransport_apply realConjugation (a.toMul : Rbar)
  rw [realAutTransport_conjugation] at h
  change realClosureEquiv
      ((show Rbar ≃ₐ[ℝ] Rbar from realConjugation) (a.toMul : Rbar)) =
      (starRingEnd ℂ) (realClosureEquiv (a.toMul : Rbar))
  exact h.symm

theorem norm_iff_positive (a : A) (ha : realBarAction realConjugation a=a) :
    (∃ u : A, realBarAction realConjugation u+u=a) ↔ 0 < (asComplexUnit a : ℂ).re := by
  have hFixed : (starRingEnd ℂ) (asComplexUnit a : ℂ) = (asComplexUnit a : ℂ) := by
    rw [← asComplexUnit_conj,ha]
  rw [← conj_fixed_norm_iff _ hFixed]
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨asComplexUnit u,?_⟩
    rw [← asComplexUnit_conj,← asComplexUnit_add,hu]
  · rintro ⟨u,hu⟩
    obtain ⟨v,rfl⟩ := asComplexUnit_surjective u
    refine ⟨v,asComplexUnit_injective (Units.ext ?_)⟩
    rw [asComplexUnit_add,asComplexUnit_conj]
    exact hu

def normalized (z : continuousCycles ℝ) : A :=
  CTCyclicTwoBar318.normalizedValue realBarAction realConjugation (onPairs z.val)

theorem normalized_fixed (z : continuousCycles ℝ) :
    realBarAction realConjugation (normalized z)=normalized z :=
  CTCyclicTwoBar318.fixed_value realBarAction realConjugation realConjugation_square
    (onPairs z.val) (isCycle_pairs z)

def signedReal (z : continuousCycles ℝ) : ℝ := (asComplexUnit (normalized z) : ℂ).re

theorem signedReal_coe (z : continuousCycles ℝ) :
    (signedReal z : ℂ) = (asComplexUnit (normalized z) : ℂ) :=
  Complex.conj_eq_iff_re.mp
    ((asComplexUnit_conj (normalized z)).symm.trans (congrArg
      (fun a : A => (asComplexUnit a : ℂ)) (normalized_fixed z)))

theorem signedReal_ne_zero (z : continuousCycles ℝ) : signedReal z≠0 := by
  intro h
  have h' := signedReal_coe z
  rw [h,Complex.ofReal_zero] at h'
  exact Units.ne_zero _ h'.symm

theorem signedReal_zero : signedReal 0=1 := by
  have h : normalized 0=0 := by
    change (0 : A)-realBarAction realConjugation 0=0
    rw [map_zero,sub_zero]
  change (asComplexUnit (normalized 0) : ℂ).re=1
  rw [h,asComplexUnit_coe]
  change (realClosureEquiv 1).re=1
  simp

theorem signedReal_add (z z' : continuousCycles ℝ) :
    signedReal (z+z')=signedReal z * signedReal z' := by
  have hn : normalized (z+z')=normalized z+normalized z' := by
    change onPairs z.val realConjugation realConjugation +
        onPairs z'.val realConjugation realConjugation -
        realBarAction realConjugation (onPairs z.val 1 1 + onPairs z'.val 1 1) =
      (onPairs z.val realConjugation realConjugation -
        realBarAction realConjugation (onPairs z.val 1 1)) +
      (onPairs z'.val realConjugation realConjugation -
        realBarAction realConjugation (onPairs z'.val 1 1))
    rw [map_add]
    abel
  apply Complex.ofReal_injective
  calc
    (signedReal (z+z') : ℂ) = (asComplexUnit (normalized (z+z')) : ℂ) :=
      signedReal_coe _
    _ = (signedReal z : ℂ) * (signedReal z' : ℂ) := by
      rw [hn,asComplexUnit_add,← signedReal_coe,← signedReal_coe]
    _ = ((signedReal z * signedReal z' : ℝ) : ℂ) := (Complex.ofReal_mul _ _).symm

/-- The Hamilton class already occurs with this exact complex sign on
the literal native two-cochain complex, not just an abstract C₂. -/
theorem exists_hamilton_cycle : ∃ z : continuousCycles ℝ, signedReal z = -1 := by
  let a : A := Additive.ofMul (Units.mk0 (-1 : Rbar) (by norm_num))
  have hv : (asComplexUnit a : ℂ) = -1 := by
    rw [asComplexUnit_coe]
    change realClosureEquiv (-1) = -1
    simp
  have ha : realBarAction realConjugation a=a := by
    apply asComplexUnit_injective
    apply Units.ext
    rw [asComplexUnit_conj,hv]
    simp
  obtain ⟨c,hc,hvC⟩ := CTCyclicTwoBar318.carry_cycle realBarAction realConjugation
    realConjugation_square realConjugation_ne_one realGal_cases a ha
  obtain ⟨z,hz⟩ := mkPairs_cycle c hc
  have ht : normalized z = a := by
    unfold normalized
    rw [hz,pairs_ofPairs,hvC]
  refine ⟨z,?_⟩
  change (asComplexUnit (normalized z) : ℂ).re = -1
  rw [ht,hv]
  simp

/-- This is the native real local Brauer-class boundary criterion,
without importing class field theory, embeddings into a discrete
replacement, or an abstract Brauer quotient of algebras. -/
theorem class_zero_iff_sign (z : continuousCycles ℝ) :
    classOf ℝ z=0 ↔ 0 < signedReal z :=
  (class_zero_iff_norm z).trans (norm_iff_positive _ (normalized_fixed z))

end CTRealNativeNormClass318
