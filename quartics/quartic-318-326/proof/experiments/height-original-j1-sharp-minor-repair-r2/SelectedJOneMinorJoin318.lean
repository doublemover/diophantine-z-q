module
public import SelectedJOneExactMinorLoss318
public import SelectedJOneLocalDegree318
public import SelectedOneDiskHadamard318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.PrimitiveElement
import all SelectedJOneExactMinorLoss318
import all SelectedJOneLocalDegree318
public section
noncomputable section
open NumberField Function Set MeasureTheory Metric
open scoped BigOperators

namespace SelectedJOneMinorJoin318

/-- The local finite frames for the original ordered algebraic minor m.
Here M is the level of the actual j-cover, not the primitive factor's
level. The dual witness is the signed VALUE at j=1, not a degree input. -/
structure FiniteFrames (L : Type*) [Field L] [NumberField L] {g : ℕ}
    (m : Matrix (Fin g) (Fin g) L) (M : ℕ) where
  C : FinitePlace L → Matrix (Fin g) (Fin g) L
  C_nonzero : ∀ v, (C v).det ≠ 0
  u : FinitePlace L → Fin g → L
  u_nonzero : ∀ v i, u v i ≠ 0
  I : (v : FinitePlace L) → Matrix (Fin g) (Fin g)
    (SelectedJOneExactMinorLoss318.integralAt v)
  frame : ∀ v, SelectedJOneExactMinorLoss318.baseMatrix v (I v) =
    Matrix.diagonal (u v) * m * C v
  finiteSupport : Finset (FinitePlace L)
  unitsOff : ∀ v ∉ finiteSupport, (∀ i, v (u v i) = 1) ∧
    v (SelectedJOneExactMinorLoss318.baseMatrix v (I v)).det = 1 ∧
    v ((m.det*(C v).det)⁻¹) = 1
  dualAtOne : ∀ v i, ∃ t : L, v t ≤ 1 ∧ u v i*t = -((1727*M : ℕ) : L)

variable {L : Type*} [Field L] [NumberField L] {g : ℕ}
    {m : Matrix (Fin g) (Fin g) L} {M : ℕ}

def FiniteFrames.evalDegree (r : FiniteFrames L m M) : ℝ :=
  SelectedJOneExactMinorLoss318.degree (fun v => (m.det*(r.C v).det)⁻¹)

def FiniteFrames.loss (r : FiniteFrames L m M) : ℝ :=
  SelectedJOneExactMinorLoss318.degree
    (fun v => (SelectedJOneExactMinorLoss318.baseMatrix v (r.I v)).det)

def FiniteFrames.column (r : FiniteFrames L m M) (i : Fin g) : ℝ :=
  SelectedJOneExactMinorLoss318.degree (fun v => r.u v i)

theorem FiniteFrames.exact (r : FiniteFrames L m M) (hm : m.det ≠ 0) :
    0 ≤ r.loss ∧ r.evalDegree = (∑ i, r.column i)-r.loss :=
  SelectedJOneExactMinorLoss318.exact_finite m hm r.C r.C_nonzero
    r.u r.u_nonzero r.I r.frame r.finiteSupport r.unitsOff

theorem FiniteFrames.column_le (r : FiniteFrames L m M) (hM : 0 < M) (i : Fin g) :
    r.column i ≤ Real.log (M : ℝ) + Real.log 1727 := by
  have hfin : HasFiniteMulSupport (fun v : FinitePlace L => v (r.u v i)) := by
    classical
    apply r.finiteSupport.finite_toSet.subset
    intro v hv
    change v ∈ r.finiteSupport
    by_contra hout
    exact hv ((r.unitsOff v hout).1 i)
  have hpos (v : FinitePlace L) : 0 < v (r.u v i) :=
    v.1.pos_iff.mpr (r.u_nonzero v i)
  have h := SelectedJOneLocalDegree318.literal_bound (fun v => r.u v i) M hM
    hfin hpos (fun v => by
      obtain ⟨t,ht,htval⟩ := r.dualAtOne v i
      refine ⟨-t, ?_, ?_⟩
      · simpa only [map_neg_eq_map] using ht
      · rw [mul_neg, htval, neg_neg])
  rw [FiniteFrames.column, SelectedJOneExactMinorLoss318.degree, finsum_neg_distrib]
  exact h

/-- The archimedean input is the actual change of the SAME algebraic
minor to the orthonormal differential basis for each complex embedding.
All unit vectors, not just the basis vectors, obey the local energy bound.
No per-embedding choice of a different minor or arbitrary weights. -/
structure ArchFrames (L : Type*) [Field L] [NumberField L] {g : ℕ}
    (m : Matrix (Fin g) (Fin g) L) where
  Z : (L →ₐ[ℚ] ℂ) → Matrix (Fin g) (Fin g) ℂ
  unit_Z : ∀ σ, IsUnit (Z σ)
  f : (L →ₐ[ℚ] ℂ) → Fin g → Fin g → ℂ → ℂ
  values : ∀ σ i j, ((σ.toRingHom.mapMatrix m)*Z σ) i j = f σ i j 0
  hol : ∀ σ i x, ‖x‖ = 1 → DifferentiableOn ℂ
    (SelectedOneDiskHadamard318.combination (f σ i) x) (ball 0 1)
  integ : ∀ σ i x, ‖x‖ = 1 → IntegrableOn
    (fun z => ‖SelectedOneDiskHadamard318.combination (f σ i) x z‖ ^ 2) (ball 0 1)
  energy : ∀ σ i x, ‖x‖ = 1 → (∫ z in ball (0 : ℂ) 1,
    ‖SelectedOneDiskHadamard318.combination (f σ i) x z‖ ^ 2) ≤ 1

/-- Each embedding is counted once; a conjugate pair thus contributes
twice. No independent set of archimedean weights is supplied. -/
def ArchFrames.degree (r : ArchFrames L m) : ℝ :=
  (∑ σ : L →ₐ[ℚ] ℂ, -Real.log ‖(σ m.det*(r.Z σ).det)⁻¹‖) /
    (Module.finrank ℚ L : ℝ)

theorem ArchFrames.embedding_bound (r : ArchFrames L m) (hm : m.det ≠ 0)
    (σ : L →ₐ[ℚ] ℂ) :
    -Real.log ‖(σ m.det*(r.Z σ).det)⁻¹‖ ≤ -(g : ℝ) * (Real.log Real.pi / 2) := by
  let A := (σ.toRingHom.mapMatrix m)*r.Z σ
  have hdet : A.det = σ m.det*(r.Z σ).det := by
    dsimp only [A]
    rw [Matrix.det_mul, ← σ.toRingHom.map_det] <;> rfl
  have hσ : σ m.det ≠ 0 := by
    intro hz
    apply hm
    apply σ.injective
    simpa only [map_zero] using hz
  have hz : (r.Z σ).det ≠ 0 := ((r.Z σ).isUnit_iff_isUnit_det.mp (r.unit_Z σ)).ne_zero
  have hn : A.det ≠ 0 := by rw [hdet]; exact mul_ne_zero hσ hz
  rw [← hdet, norm_inv, Real.log_inv, neg_neg]
  exact SelectedOneDiskHadamard318.logdet A (r.f σ) (r.values σ)
    (r.hol σ) (r.integ σ) (r.energy σ) hn

theorem ArchFrames.bound (r : ArchFrames L m) (hm : m.det ≠ 0) :
    r.degree ≤ -(g : ℝ) * (Real.log Real.pi / 2) := by
  let b := -(g : ℝ) * (Real.log Real.pi / 2)
  have hd : (0:ℝ) < (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=L))
  have hc : Fintype.card (L →ₐ[ℚ] ℂ) = Module.finrank ℚ L := AlgHom.card ℚ L ℂ
  unfold ArchFrames.degree
  change _ ≤ b
  calc
    _ ≤ (∑ _σ : L →ₐ[ℚ] ℂ, b)/(Module.finrank ℚ L : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _ => r.embedding_bound hm σ)) hd.le
    _ = b := by
      rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      exact (div_eq_iff hd.ne').mpr (mul_comm _ _)

/-- Exact assembly at one already chosen nonsingular j=1 minor.
The geometric determinant-degree/height identification is the named
remaining input, not a conclusion from a generic field or a mock chart. -/
theorem sharp_height (rf : FiniteFrames L m M) (ra : ArchFrames L m)
    (hm : m.det ≠ 0) (hM : 0 < M) (h0 hplus : ℝ)
    (degree_identity : h0 = rf.evalDegree + ra.degree)
    (metric_shift : hplus = h0 + (g : ℝ) * (Real.log Real.pi / 2)) :
    hplus ≤ (g : ℝ) * Real.log (1727*(M : ℝ)) := by
  obtain ⟨hl, hf⟩ := rf.exact hm
  have h := SelectedOneDiskHadamard318.shift_cancel
    rf.column (Real.log (M : ℝ)+Real.log 1727) rf.loss ra.degree h0 hplus
    (rf.column_le hM) hl (by rw [degree_identity,hf])
    (ra.bound hm) metric_shift
  have hMp : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  rw [Real.log_mul (by norm_num) hMp.ne', add_comm (Real.log 1727)]
  exact h

end SelectedJOneMinorJoin318
#print axioms SelectedJOneMinorJoin318.FiniteFrames.exact
#print axioms SelectedJOneMinorJoin318.ArchFrames.bound
#print axioms SelectedJOneMinorJoin318.sharp_height
