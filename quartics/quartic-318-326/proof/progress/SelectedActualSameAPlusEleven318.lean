module
public import RationalSectionHeight318
public import InducedLattice318
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Direct +11 receiver, *not* the normalized modular Jacobian.
At an actual identity chart E over the height field L, the cotangent fibre
is L ⊗[E] Ω(E/L), with the E action on L specified by its identity point.
The period volume and primitive-coframe identifications are inputs, not
consequences of the unrelated finite trace algebra. -/
public section
noncomputable section

open NumberField SectionHeight318
open scoped TensorProduct Matrix

namespace SelectedActualSameAPlusEleven318

abbrev clearing : ℕ := 1189580636160000
abbrev Dzero : ℕ := 2765952000

section Fiber
variable {L E : Type*} [Field L] [NumberField L] [CommRing E] [Algebra L E]

/-- Specialization of the actual affine cotangent module at the named point.
The base algebra E→L is local, never a second global scalar instance. -/
abbrev Cotangent (ε : E →ₐ[L] L) : ModuleCat L := by
  letI : Algebra E L := ε.toRingHom.toAlgebra
  exact ModuleCat.of L (L ⊗[E] KaehlerDifferential L E)

/-- Same rational coframe is used at every place. The finite bases are the
generic readings of the primitive-trait coframes and the real matrices
must be the real period columns for that very same rational coframe. -/
structure LocalFrames (ε : E →ₐ[L] L) where
  rational : Module.Basis (Fin 2) L (Cotangent ε)
  primitive : FinitePlace L → Module.Basis (Fin 2) L (Cotangent ε)
  det_ne : ∀ w, ((primitive w).toMatrix rational).det ≠ 0
  almost_unit : Function.HasFiniteMulSupport
    (fun w : FinitePlace L => w (((primitive w).toMatrix rational).det))
  periods : InfinitePlace L → Matrix (Fin 4) (Fin 4) ℝ
  period_nonsingular : ∀ w, (periods w).det ≠ 0

variable {ε : E →ₐ[L] L} (H : LocalFrames ε)

namespace LocalFrames

abbrev wedgeCoeff (w : FinitePlace L) : L := ((H.primitive w).toMatrix H.rational).det

/-- In complex dimension two, the (2π)^(-2) squared norm converts
4 times real volume to volume / π². This is the shifted metric, not JV. -/
@[expose] def periodSquare (w : InfinitePlace L) : ℝ := |(H.periods w).det| / Real.pi ^ 2

theorem periodSquare_pos (w : InfinitePlace L) : 0 < H.periodSquare w := by
  exact div_pos (abs_pos.mpr (H.period_nonsingular w)) (pow_pos Real.pi_pos _)

@[expose] def frame : FrameNorms L where
  finiteNorm w := w (H.wedgeCoeff w)
  finite_pos w := w.val.pos (H.det_ne w)
  finite_support := H.almost_unit
  arch w := Real.sqrt (H.periodSquare w)
  arch_pos w := Real.sqrt_pos.2 (H.periodSquare_pos w)

theorem square_arch (w : InfinitePlace L) :
    (InducedLattice318.square H.frame).arch w = H.periodSquare w :=
  Real.sq_sqrt (H.periodSquare_pos w).le

theorem square_finite (w : FinitePlace L) :
    (InducedLattice318.square H.frame).finiteNorm w = w (H.wedgeCoeff w) ^ 2 := rfl

end LocalFrames

/-- q is the coefficient of Ψ⁻¹(210 Q) in the square of the named rational
determinant frame. It already contains the archimedean 210; no finite 210
is introduced here. t is the actual rational 32u/v; its ratio is t/32. -/
def factor (t : ℚ) (i : Fin 2) : L := ![32,(t : L)] i
def raw (t : ℚ) (q : L) (i : Fin 2) : L := factor (L := L) t i * (Dzero : L)^2 * q
def scaled (t : ℚ) (q : L) (i : Fin 2) : L := raw t q i / (clearing : L)

namespace LocalFrames

/-- Finite input is divisibility *in the primitive wedge frame* following
integral Θ=Ψ/210 and pullback to the proper trait, not a local norm bound. -/
theorem finite_from_primitive (t : ℚ) (q : L) (w : FinitePlace L) (i : Fin 2)
    (z : L) (hz : w z ≤ 1)
    (he : raw t q i * (H.wedgeCoeff w)^2 = (clearing : L) * z) :
    w (scaled t q i) * (InducedLattice318.square H.frame).finiteNorm w ≤ 1 := by
  have h : scaled t q i * (H.wedgeCoeff w)^2 = z := by
    unfold scaled
    have hc : (clearing : L) ≠ 0 := by norm_num [clearing]
    field_simp [hc]
    linear_combination he
  rw [H.square_finite,← map_pow,← map_mul,h]
  exact hz

/-- Geometric input at infinity is the calibrated norm of the single Q,
not two norm bounds or the final logarithmic inequality. -/
theorem arch_from_calibration (t : ℚ) (q : L) (w : InfinitePlace L) (i : Fin 2)
    (U f : ℝ) (hU : 2 * max (32 : ℝ) (w (t : L)) ≤ U) (hf : 64 ≤ f)
    (hq : w q * H.periodSquare w = 210 * 4 / (U*f)) :
    w (scaled t q i) * (InducedLattice318.square H.frame).arch w ≤ 2701125/64 := by
  have hU' : 0 < U := by linarith [le_max_left (32:ℝ) (w (t:L))]
  have hf' : 0 < f := by linarith
  have hfac : w (factor (L := L) t i) ≤ max 32 (w (t : L)) := by
    fin_cases i
    · change w (32 : L) ≤ _
      have h32 := w.map_natCast 32
      simpa only [Nat.cast_ofNat] using h32.le.trans
        (le_max_left ((32 : ℕ) : ℝ) (w (t:L)))
    · exact le_max_right _ _
  have hC : w (clearing : L) = (clearing : ℝ) := w.map_natCast clearing
  have hD : w (Dzero : L) = (Dzero : ℝ) := w.map_natCast Dzero
  have hfac' : 2 * w (factor (L := L) t i) ≤ U :=
    (mul_le_mul_of_nonneg_left hfac (by norm_num)).trans hU
  have hden : 128 * w (factor (L := L) t i) ≤ U*f := by
    calc
      _ = (2*w (factor (L := L) t i))*64 := by ring
      _ ≤ U*64 := mul_le_mul_of_nonneg_right hfac' (by norm_num)
      _ ≤ U*f := mul_le_mul_of_nonneg_left hf hU'.le
  have hx : w (scaled t q i) * (InducedLattice318.square H.frame).arch w =
      (w (factor (L := L) t i) * (Dzero : ℝ)^2 / (clearing : ℝ)) *
        (210*4 / (U*f)) := by
    rw [H.square_arch,← hq]
    unfold scaled raw
    rw [map_div₀,map_mul,map_mul,map_pow,hC,hD]
    ring
  rw [hx]
  have hp : 0 < U*f := mul_pos hU' hf'
  rw [show (w (factor (L := L) t i) * (Dzero : ℝ)^2 / (clearing : ℝ)) *
        (210*4/(U*f)) = (w (factor (L := L) t i)*5402250)/(U*f) by
    norm_num [clearing,Dzero]
    ring]
  apply (div_le_iff₀ hp).2
  linarith only [hden]

end LocalFrames

theorem log_factor_lt : Real.log ((2701125:ℝ)/64) < 11 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h : (8:ℝ)/3 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : ((8:ℝ)/3)^11 < (Real.exp 1)^11 :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  calc
    _ < ((8:ℝ)/3)^11 := by norm_num
    _ < (Real.exp 1)^11 := hp
    _ = Real.exp 11 := by rw [← Real.exp_nat_mul]; norm_num

/-- Feed each finite place its proper-trait divisibility certificate, and
each infinite place its matrix of periods and the original Petersson
isometry. Taking degree on L itself avoids a false K=L substitution. -/
theorem height_of_local_data (t : ℚ) (q : L) (qne : q ≠ 0)
    (hfin : ∀ (w : FinitePlace L) (i : Fin 2), ∃ z : L, w z ≤ 1 ∧
      raw t q i * (H.wedgeCoeff w)^2 = (clearing : L) * z)
    (hinf : ∀ w : InfinitePlace L, ∃ U f : ℝ,
      2 * max (32:ℝ) (w (t:L)) ≤ U ∧ 64 ≤ f ∧
      w q * H.periodSquare w = 210*4/(U*f)) :
    Height.logHeight₁ (t/32) < 2 * H.frame.normalizedDegree + 11 := by
  have h0 : scaled t q 0 ≠ 0 := by
    change (32 : L) * (Dzero : L)^2 * q / (clearing : L) ≠ 0
    exact div_ne_zero (mul_ne_zero (by norm_num [Dzero]) qne) (by norm_num [clearing])
  have hr : scaled t q 1 = ((t/32:ℚ) : L) * scaled t q 0 := by
    change (t:L) * (Dzero:L)^2 * q / (clearing:L) =
      ((t/32:ℚ):L) * ((32:L) * (Dzero:L)^2 * q / (clearing:L))
    push_cast
    ring
  have he : (![scaled t q 0, scaled t q 1] : Fin 2 → L) = scaled t q := by
    funext i
    fin_cases i <;> rfl
  have hall := SectionHeight318.rational_section_height
    (scaled t q 0) (scaled t q 1) (t/32) h0 hr (InducedLattice318.square H.frame)
    (2701125/64)
    (fun w i => by
      rw [he]
      obtain ⟨U,f,hu,hf,hq⟩ := hinf w
      exact H.arch_from_calibration t q w i U f hu hf hq)
    (fun w i => by
      rw [he]
      obtain ⟨z,hz,hv⟩ := hfin w i
      exact H.finite_from_primitive t q w i z hz hv)
  rw [InducedLattice318.square_degree] at hall
  exact hall.trans_lt (by linarith only [log_factor_lt])

end Fiber
end SelectedActualSameAPlusEleven318
