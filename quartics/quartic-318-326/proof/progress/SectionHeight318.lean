module
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.NumberTheory.Height.Projectivization
public section
noncomputable section
open NumberField Height Real
namespace SectionHeight318
set_option maxHeartbeats 0
variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Finite ι]

/-- The actual local maximum of the absolute values of the coordinates. -/
@[expose] def localMax (v : AbsoluteValue K ℝ) (a : ι → K) : ℝ := ⨆ i, v (a i)

omit [NumberField K] in
theorem localMax_pos (v : AbsoluteValue K ℝ) {a : ι → K} (ha : a ≠ 0) :
    0 < localMax v a := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  exact (v.pos hi).trans_le (Finite.le_ciSup_of_le i le_rfl)

theorem finite_localMax_support {a : ι → K} (ha : a ≠ 0) :
    Function.HasFiniteMulSupport (fun v : FinitePlace K => localMax v.val a) := by
  have : Nonempty {j // a j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp ha
  suffices (fun v : FinitePlace K => ⨆ i : {j // a j ≠ 0}, v (a i)).HasFiniteMulSupport by
    convert! this with v
    obtain ⟨i, hi⟩ : ∃ j, a j ≠ 0 := Function.ne_iff.mp ha
    have : Nonempty ι := ⟨i⟩
    refine le_antisymm (ciSup_le fun j => ?_) (ciSup_le fun ⟨j, hj⟩ => Finite.le_ciSup_of_le j le_rfl)
    rcases eq_or_ne (a j) 0 with h | h
    · rw [h, map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  exact Function.HasFiniteMulSupport.iSup (fun i => FinitePlace.hasFiniteMulSupport i.prop)

theorem log_finite_support {α : Type*} {f : α → ℝ}
    (hf : Function.HasFiniteMulSupport f) :
    Function.HasFiniteSupport (fun i => Real.log (f i)) := by
  apply hf.subset
  intro i hi
  simp only [Function.mem_support, Function.mem_mulSupport] at hi ⊢
  intro he
  exact hi (by simp [he])

theorem logHeight_places {a : ι → K} (ha : a ≠ 0) :
    Height.logHeight a =
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (localMax v.val a)) +
      ∑ᶠ v : FinitePlace K, Real.log (localMax v.val a) := by
  classical
  have hp : ∀ v : AbsoluteValue K ℝ, 0 < localMax v a := fun v => localMax_pos v ha
  rw [Height.logHeight, NumberField.mulHeight_eq ha]
  change Real.log ((∏ v : InfinitePlace K, localMax v.val a ^ v.mult) *
    ∏ᶠ v : FinitePlace K, localMax v.val a) = _
  have hA : (∏ v : InfinitePlace K, localMax v.val a ^ v.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hp v.val).ne')
  have hB : (∏ᶠ v : FinitePlace K, localMax v.val a) ≠ 0 :=
    finprod_ne_zero (fun (v : FinitePlace K) => (hp v.val).ne')
  rw [Real.log_mul hA hB]
  rw [Real.log_prod (f := fun v : InfinitePlace K => localMax v.val a ^ v.mult)
    (fun v _ => pow_ne_zero _ (hp v.val).ne')]
  rw [Real.log_finprod (f := fun v : FinitePlace K => localMax v.val a) (fun v => hp v.val)]
  simp only [Real.log_pow]

/-- Local norms of one nonzero rational frame of a metrized line.
The finite-support condition is the adelic finiteness of its divisor. -/
structure FrameNorms (K : Type*) [Field K] [NumberField K] where
  arch : InfinitePlace K → ℝ
  finiteNorm : FinitePlace K → ℝ
  arch_pos : ∀ v, 0 < arch v
  finite_pos : ∀ v, 0 < finiteNorm v
  finite_support : Function.HasFiniteMulSupport finiteNorm

@[expose] def FrameNorms.logSum (F : FrameNorms K) : ℝ :=
  (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (F.arch v)) +
  ∑ᶠ v : FinitePlace K, Real.log (F.finiteNorm v)

/-- Normalized Arakelov degree expressed in a rational frame. -/
@[expose] def FrameNorms.normalizedDegree (F : FrameNorms K) : ℝ :=
  - F.logSum / (Module.finrank ℚ K : ℝ)

/-- Absolute normalization of Mathlib's actual projective height. -/
@[expose] def absoluteProjectiveHeight (P : Projectivization K (ι → K)) : ℝ :=
  Projectivization.logHeight P / (Module.finrank ℚ K : ℝ)

theorem local_log_bound (v : AbsoluteValue K ℝ) {a : ι → K} (ha : a ≠ 0)
    {r C : ℝ} (hr : 0 < r) (hsection : ∀ i, v (a i) * r ≤ C) :
    Real.log (localMax v a) + Real.log r ≤ Real.log C := by
  have : Nonempty ι := (Function.ne_iff.mp ha).nonempty
  have hb : localMax v a * r ≤ C := by
    apply (le_div_iff₀ hr).mp
    exact ciSup_le (fun i => (le_div_iff₀ hr).mpr (hsection i))
  have h := Real.log_le_log (mul_pos (localMax_pos v ha) hr) hb
  rwa [Real.log_mul (localMax_pos v ha).ne' hr.ne'] at h

/-- Actual all-place section-height inequality before absolute normalization.
The finite inequalities allow common vertical zeros; they need not be equalities. -/
theorem section_height_relative {a : ι → K} (ha : a ≠ 0) (F : FrameNorms K)
    (C : ℝ)
    (harch : ∀ (v : InfinitePlace K) i, v (a i) * F.arch v ≤ C)
    (hfinite : ∀ (v : FinitePlace K) i, v (a i) * F.finiteNorm v ≤ 1) :
    Height.logHeight a ≤ - F.logSum + (Module.finrank ℚ K : ℝ) * Real.log C := by
  classical
  have ha' : ∀ v : InfinitePlace K,
      (v.mult : ℝ) * (Real.log (localMax v.val a) + Real.log (F.arch v)) ≤
        (v.mult : ℝ) * Real.log C := fun v =>
    mul_le_mul_of_nonneg_left (local_log_bound v.val ha (F.arch_pos v) (harch v))
      (by positivity)
  have hasum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => ha' v)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Nat.cast_sum, InfinitePlace.sum_mult_eq] at hasum
  have hfs := log_finite_support (finite_localMax_support ha)
  have hFr := log_finite_support F.finite_support
  have hf' : (fun v : FinitePlace K =>
      Real.log (localMax v.val a) + Real.log (F.finiteNorm v)) ≤ 0 := by
    intro v
    simpa using local_log_bound v.val ha (F.finite_pos v) (hfinite v)
  have hfsum := finsum_le_finsum (hfs.add hFr) (by fun_prop) hf'
  simp only [Pi.add_apply] at hfsum
  rw [finsum_add_distrib hfs hFr] at hfsum
  simp only [Pi.zero_apply, finsum_zero] at hfsum
  rw [logHeight_places ha]
  unfold FrameNorms.logSum
  linarith

/-- Two (or any finite number of) integral sections bounded by C at infinity
bound the actual projective height by line degree plus log C. -/
theorem section_height {a : ι → K} (ha : a ≠ 0) (F : FrameNorms K)
    (C : ℝ)
    (harch : ∀ (v : InfinitePlace K) i, v (a i) * F.arch v ≤ C)
    (hfinite : ∀ (v : FinitePlace K) i, v (a i) * F.finiteNorm v ≤ 1) :
    absoluteProjectiveHeight (Projectivization.mk K a ha) ≤
      F.normalizedDegree + Real.log C := by
  have hd : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast Module.finrank_pos
  have h := section_height_relative ha F C harch hfinite
  unfold absoluteProjectiveHeight FrameNorms.normalizedDegree
  rw [Projectivization.logHeight_mk]
  apply (div_le_iff₀ hd).mpr
  have he : (-F.logSum / (Module.finrank ℚ K : ℝ) + Real.log C) *
      (Module.finrank ℚ K : ℝ) = -F.logSum + (Module.finrank ℚ K : ℝ) * Real.log C := by
    field_simp
  rwa [he]

/-- The scalar product formula in logarithmic form, with the actual place weights. -/
theorem scalar_log_sum_zero (c : K) (hc : c ≠ 0) :
    (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v.val c)) +
      (∑ᶠ v : FinitePlace K, Real.log (v.val c)) = 0 := by
  have h := logHeight_places (a := fun _ : Unit => c) (by
    intro he
    exact hc (congrFun he ()))
  simpa [localMax, Height.logHeight_eq_zero_of_subsingleton] using h.symm

/-- Change the rational frame ell to c * ell. -/
@[expose] def FrameNorms.rescale (F : FrameNorms K) (c : K) (hc : c ≠ 0) : FrameNorms K where
  arch v := v.val c * F.arch v
  finiteNorm v := v.val c * F.finiteNorm v
  arch_pos v := mul_pos (v.val.pos hc) (F.arch_pos v)
  finite_pos v := mul_pos (v.val.pos hc) (F.finite_pos v)
  finite_support := (FinitePlace.hasFiniteMulSupport hc).mul F.finite_support

/-- The normalized line degree is genuinely independent of its rational frame. -/
theorem FrameNorms.normalizedDegree_rescale (F : FrameNorms K) (c : K) (hc : c ≠ 0) :
    (F.rescale c hc).normalizedDegree = F.normalizedDegree := by
  classical
  have hfin := log_finite_support (FinitePlace.hasFiniteMulSupport hc)
  have hFr := log_finite_support F.finite_support
  unfold FrameNorms.normalizedDegree FrameNorms.logSum FrameNorms.rescale
  have hca : ∀ v : InfinitePlace K, v.val c ≠ 0 := fun v => v.val.ne_zero_iff.mpr hc
  have hcf : ∀ v : FinitePlace K, v.val c ≠ 0 := fun v => v.val.ne_zero_iff.mpr hc
  have ha : (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v.val c * F.arch v)) =
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v.val c)) +
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (F.arch v)) := by
    simp_rw [Real.log_mul (hca _) (F.arch_pos _).ne', mul_add]
    rw [Finset.sum_add_distrib]
  have hf : (∑ᶠ v : FinitePlace K, Real.log (v.val c * F.finiteNorm v)) =
      (∑ᶠ v : FinitePlace K, Real.log (v.val c)) +
      (∑ᶠ v : FinitePlace K, Real.log (F.finiteNorm v)) := by
    simp_rw [Real.log_mul (hcf _) (F.finite_pos _).ne']
    exact finsum_add_distrib hfin hFr
  rw [ha, hf]
  have hz := scalar_log_sum_zero c hc
  congr 2
  linarith

/-- Exact all-place identity; finite common zeros contribute nonpositive terms
under the integrality hypothesis rather than creating an omitted error. -/
theorem section_log_identity {a : ι → K} (ha : a ≠ 0) (F : FrameNorms K) :
    Height.logHeight a = - F.logSum +
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (localMax v.val a * F.arch v)) +
      ∑ᶠ v : FinitePlace K, Real.log (localMax v.val a * F.finiteNorm v) := by
  classical
  have hp := fun v : AbsoluteValue K ℝ => (localMax_pos v ha).ne'
  have hf := log_finite_support (finite_localMax_support ha)
  have hFr := log_finite_support F.finite_support
  have hfadd : (∑ᶠ v : FinitePlace K, Real.log (localMax v.val a * F.finiteNorm v)) =
      (∑ᶠ v : FinitePlace K, Real.log (localMax v.val a)) +
      (∑ᶠ v : FinitePlace K, Real.log (F.finiteNorm v)) := by
    simp_rw [Real.log_mul (hp _) (F.finite_pos _).ne']
    exact finsum_add_distrib hf hFr
  have haadd : (∑ v : InfinitePlace K, (v.mult : ℝ) *
      Real.log (localMax v.val a * F.arch v)) =
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (localMax v.val a)) +
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (F.arch v)) := by
    simp_rw [Real.log_mul (hp _) (F.arch_pos _).ne', mul_add]
    exact Finset.sum_add_distrib
  rw [logHeight_places ha, hfadd, haadd]
  unfold FrameNorms.logSum
  ring

end SectionHeight318
