module
public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing
public section

namespace ActualGaussianWeberComplexFibreSeed318

open Polynomial

/-- Countability of a fraction field needs no finite-dimensional geometry.
For the original Gaussian base use the surjection ℤ × ℤ → GaussianInt. -/
theorem fraction_countable (A F : Type*) [CommRing A] [Countable A]
    [Field F] [Algebra A F] [IsFractionRing A F] : Countable F := by
  let g : A × A → F := fun v => (algebraMap A F v.1) / (algebraMap A F v.2)
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨x,y,_,h⟩ := IsFractionRing.div_surjective A z
    exact ⟨(x,y),h⟩
  exact hg.countable

variable {K : Type*} [Field K] [Algebra K ℂ]

/-- Choose a target complex abscissa avoiding every algebraic value
over the actual original coefficient field, not over ℂ itself. -/
theorem exists_transcendental_complex [Countable K] :
    ∃ c : ℂ, Transcendental K c := by
  have hAlg : ({c : ℂ | IsAlgebraic K c} : Set ℂ).Countable := Algebraic.countable K ℂ
  have hReal : Set.MapsTo Complex.ofReal (Set.univ : Set ℝ) (Set.univ : Set ℂ) :=
    fun _ _ => Set.mem_univ _
  have hNot : ¬ (Set.univ : Set ℂ).Countable := by
    intro h
    exact Cardinal.not_countable_real
      (hReal.countable_of_injOn Complex.ofReal_injective.injOn h)
  have hne : ({c : ℂ | IsAlgebraic K c} : Set ℂ) ≠ Set.univ :=
    fun e => hNot (e ▸ hAlg)
  exact (Set.ne_univ_iff_exists_notMem _).mp hne

private theorem eval_mem_alg (A : K[X]) {x : ℂ} (hx : IsAlgebraic K x) :
    A.eval₂ (algebraMap K ℂ) x ∈ algebraicClosure K ℂ := by
  let S := (algebraicClosure K ℂ).toSubalgebra
  have hx' : x ∈ S := mem_algebraicClosure_iff.mpr hx
  let y : S := ⟨x,hx'⟩
  have hY : ((aeval y A : S) : ℂ) ∈ S := (aeval y A).property
  have h : aeval x A ∈ S := by
    simpa only [y,coe_aeval_mk_apply] using hY
  change A.eval₂ (algebraMap K ℂ) x ∈ S
  simpa only [aeval_def] using h

/-- At each root of the same actual inverse fibre, the denominator does
not vanish and evaluating the original polynomial ring is injective.
Thus either actual ordinate provides a genuine embedding of the original
function field into ℂ. This avoids a separate regular-point Laurent arc. -/
theorem fibre_root_transcendental
    (A B : K[X]) (hAB : IsCoprime A B) {c x : ℂ} (hc : Transcendental K c)
    (hx : A.eval₂ (algebraMap K ℂ) x = c * B.eval₂ (algebraMap K ℂ) x) :
    B.eval₂ (algebraMap K ℂ) x ≠ 0 ∧
      Function.Injective (eval₂RingHom (algebraMap K ℂ) x) := by
  let E := eval₂RingHom (algebraMap K ℂ) x
  have hb : E B ≠ 0 := by
    intro hB
    have hA : E A = 0 := by
      change E A = c * E B at hx
      rw [hB,mul_zero] at hx
      exact hx
    obtain ⟨u,v,h⟩ := hAB
    have he : E (u*A+v*B)=E 1 := congrArg E h
    simp only [map_add,map_mul,hA,hB,mul_zero,zero_add,map_one] at he
    exact zero_ne_one he
  refine ⟨hb,?_⟩
  apply (transcendental_iff_injective (R:=K)).mp
  intro ha
  apply hc
  have hr : A.eval₂ (algebraMap K ℂ) x / B.eval₂ (algebraMap K ℂ) x = c :=
    (div_eq_iff hb).mpr hx
  have hmem := (algebraicClosure K ℂ).div_mem (eval_mem_alg A ha) (eval_mem_alg B ha)
  rw [hr] at hmem
  exact mem_algebraicClosure_iff.mp hmem

end ActualGaussianWeberComplexFibreSeed318
