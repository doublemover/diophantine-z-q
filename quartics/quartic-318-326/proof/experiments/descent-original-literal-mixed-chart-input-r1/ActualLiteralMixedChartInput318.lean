module
public import ActualChartSupportedJets318
import all Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import all ActualPureChartAxes318
public section
noncomputable section
namespace ActualLiteralMixedChartInput318

open MeasureTheory Set
open scoped ContDiff SchwartzMap
open ActualTubeAnnulusChart318 ActualTubeChartSupport318
open ActualTubeChartPoissonInput318 ActualPureChartAxes318
open ActualOrderedChartJets318 ActualChartSupportedJets318

/-- The exact ordered ∂Z^m∂T^n of U; no V derivative in its L¹ fields. -/
theorem ZT_eq (κ τ X T V : ℝ) (i : Fin 4) (m n : ℕ) (Z : ℝ) :
    iteratedDeriv m (fun z => DY (W κ τ i X) n z T V) Z =
      steps .z m (steps .t n (actual κ τ i)) (X,Z,T,V) := by
  simp only [Tjet_eq,Tjet]
  exact congrFun (iterated_line .z X (V,T)
    (steps_smooth .t (actual_contDiff κ τ i) n) m) Z

/-- The flat selector band makes the entire fixed-X chart empty,
also at |X|=1/8. This conclusion is only about free Z,T derivatives;
it needs no open neighborhood at the endpoint in the X direction. -/
theorem ZT_fixed_empty (κ τ X T V : ℝ) (i : Fin 4) (m n : ℕ) (Z : ℝ)
    (hX : |X| ≤ 1/8) :
    iteratedDeriv m (fun z => DY (W κ τ i X) n z T V) Z = 0 := by
  have h (z : ℝ) : DY (W κ τ i X) n z T V = 0 := by
    apply iteratedDeriv_zero_of_zero_germ _ n
    filter_upwards [] with t
    simp only [W,section_zero_small κ τ i X z t V hX,Complex.ofReal_zero]
  apply iteratedDeriv_zero_of_zero_germ _ m
  filter_upwards [] with z
  exact h z

private theorem zt_zero {κ τ X Z T V : ℝ} {i : Fin 4} (hτ : 0 < τ)
    (m n : ℕ) (hZ : 4 < |Z|) :
    iteratedDeriv m (fun z => DY (W κ τ i X) n z T V) Z = 0 := by
  rw [ZT_eq]
  apply actual_ordered_outside κ τ i .z .t m n hτ
  intro hp
  exact (not_le_of_gt hZ) (mem_symmetric.mp hp.2.1)

private theorem zt_continuous (κ τ X T V : ℝ) (i : Fin 4) (m n : ℕ) :
    Continuous (iteratedDeriv m (fun z => DY (W κ τ i X) n z T V)) := by
  simp only [Tjet_eq,Tjet]
  have he := iterated_line .z X (V,T) (steps_smooth .t (actual_contDiff κ τ i) n) m
  change Continuous (iteratedDeriv m (fun z =>
    steps .t n (actual κ τ i) (point .z X (V,T) z)))
  rw [he]
  exact (steps_smooth .z (steps_smooth .t (actual_contDiff κ τ i) n) m).continuous.comp
    (by fun_prop : Continuous (fun z : ℝ => (X,z,T,V)))

private theorem compact_of_z_box (f : ℝ → ℂ) (hz : ∀ z, 4 < |z| → f z = 0) :
    HasCompactSupport f := by
  have hs : Function.support f ⊆ Icc (-4) 4 := by
    intro z h
    by_contra hbox
    have ha : ¬ |z| ≤ 4 := fun hle => hbox (mem_symmetric.mpr hle)
    exact h (hz z (lt_of_not_ge ha))
  change IsCompact (closure (Function.support f))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal hs isClosed_Icc)

private theorem zt_L1 (κ τ X T V : ℝ) (i : Fin 4) (m n : ℕ)
    (hτ : 0 < τ) (J : ℝ) (hb : ∀ p, ‖steps .z m (steps .t n (actual κ τ i)) p‖ ≤ J) :
    (∫ z, ‖iteratedDeriv m (fun x => DY (W κ τ i X) n x T V) z‖) ≤ 8*J := by
  let f := iteratedDeriv m (fun x => DY (W κ τ i X) n x T V)
  have hz : ∀ z, 4 < |z| → f z = 0 := fun z h => zt_zero hτ m n h
  have hi : Integrable f :=
    (zt_continuous κ τ X T V i m n).integrable_of_hasCompactSupport (compact_of_z_box f hz)
  exact L1_box f hi J (fun z => (congrArg norm (ZT_eq κ τ X T V i m n z)).le.trans
    (hb (X,z,T,V))) hz

/-- Build the other Schwartz row from the ordered T² derivative, without
using hypothetical smoothness of a partially Fourier-transformed row. -/
def xrowYY (κ τ X T V : ℝ) (i : Fin 4) (hτ : 0 < τ) : 𝓢(ℝ,ℂ) := by
  let f := fun z => DY (W κ τ i X) 2 z T V
  have hz : ∀ z, 4 < |z| → f z = 0 := by
    intro z h
    simpa only [iteratedDeriv_zero] using zt_zero (κ := κ) (i := i)
      (X := X) (T := T) (V := V) hτ 0 2 h
  have hd : ContDiff ℝ ∞ f := by
    simp only [f,Tjet_eq,Tjet]
    exact (steps_smooth .t (actual_contDiff κ τ i) 2).comp
      (by fun_prop : ContDiff ℝ ∞ (fun z : ℝ => (X,z,T,V)))
  exact (compact_of_z_box f hz).toSchwartzMap hd

private theorem xrowYY_val (κ τ X T V : ℝ) (i : Fin 4) (hτ : 0 < τ) (z : ℝ) :
    xrowYY κ τ X T V i hτ z = DY (W κ τ i X) 2 z T V := by
  unfold xrowYY <;> rfl

theorem xrowYY_eq (κ τ X T V : ℝ) (i : Fin 4) (hτ : 0 < τ) :
    (xrowYY κ τ X T V i hτ : ℝ → ℂ) = fun z => DY (W κ τ i X) 2 z T V :=
  funext (xrowYY_val κ τ X T V i hτ)

/-- The actual mixed chart producer. J₀,J₂,J₄ are fixed before X.
The V exterior clause uses the literal τ≤1 bridge. -/
theorem uniform_actual_input (κ τ : ℝ) (i : Fin 4)
    (hτ : 0 < τ) (hτu : τ ≤ 1) :
    ∃ J₀ J₂ J₄ : ℝ, ∀ X : ℝ, Nonempty (Input κ τ i X J₀ J₂ J₄) := by
  obtain ⟨J₀,h₀,b₀⟩ := actual_ordered_uniform κ τ i .z .t 0 0 hτ
  obtain ⟨Jx,hx,bx⟩ := actual_ordered_uniform κ τ i .z .t 2 0 hτ
  obtain ⟨Jy,_,bT⟩ := actual_ordered_uniform κ τ i .z .t 0 2 hτ
  obtain ⟨J₄,h₄,b₄⟩ := actual_ordered_uniform κ τ i .z .t 2 2 hτ
  let J₂ := max Jx Jy
  refine ⟨J₀,J₂,J₄,fun X => ⟨{ xrow := fun y z => xrow κ τ i X y z hτ
    xrow_eq := fun y z => ActualTubeChartSupport318.xrow_eq κ τ i X y z hτ
    xrowYY := fun y z => xrowYY κ τ X y z i hτ
    xrowYY_eq := fun y z => xrowYY_eq κ τ X y z i hτ
    yjet := actual_yjet κ τ X i hτ
    zjet := actual_zjet κ τ X i hτ
    yzero := ?_, yzero₂ := ?_, zzero := ?_
    nonneg₀ := zero_le_one.trans h₀
    nonneg₂ := zero_le_one.trans (hx.trans (le_max_left _ _))
    nonneg₄ := zero_le_one.trans h₄
    L₀ := ?_, L₂x := ?_, L₂y := ?_, L₄ := ?_ }⟩⟩
  · intro x y z hy
    simp only [W,section_zero_T hτ hy,Complex.ofReal_zero]
  · intro x y z hy
    exact support_Y κ τ i X x y z hτ hy 2
  · intro x y z hz
    have hz' : 2*τ ≤ |z| := by linarith
    simp only [W,section_zero_V hτ hz',Complex.ofReal_zero]
  · intro y z
    simpa only [iteratedDeriv_zero,DY,ActualTubeChartSupport318.xrow_eq,W] using zt_L1 κ τ X y z i 0 0 hτ J₀ b₀
  · intro y z
    have hB : ∀ p, ‖steps .z 2 (steps .t 0 (actual κ τ i)) p‖ ≤ J₂ :=
      fun p => (bx p).trans (le_max_left _ _)
    simpa only [iteratedDeriv_zero,DY,ActualTubeChartSupport318.xrow_eq,W] using zt_L1 κ τ X y z i 2 0 hτ J₂ hB
  · intro y z
    have hB : ∀ p, ‖steps .z 0 (steps .t 2 (actual κ τ i)) p‖ ≤ J₂ :=
      fun p => (bT p).trans (le_max_right _ _)
    simpa only [iteratedDeriv_zero,xrowYY_eq] using zt_L1 κ τ X y z i 0 2 hτ J₂ hB
  · intro y z
    simpa only [xrowYY_eq] using zt_L1 κ τ X y z i 2 2 hτ J₄ b₄

end ActualLiteralMixedChartInput318
