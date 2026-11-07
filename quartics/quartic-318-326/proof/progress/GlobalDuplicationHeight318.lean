module
public import DuplicationInfiniteProduct318
public import AbsoluteHeightNormalization318
public section
namespace GlobalDuplicationHeight318
open ConcreteG8Domain LocalGenerator318 NumberField RelativeDuplicationHeight318 DuplicationProjective318
open DuplicationFiniteProduct318 DuplicationInfiniteProduct318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

lemma iSup_fin_two (v:K→ℝ) (x:Fin 2→K) : (⨆i,v (x i))=max (v (x 0)) (v (x 1)) := by
  apply eq_of_forall_ge_iff
  intro r
  simp [ciSup_le_iff,Fin.forall_fin_two]

lemma mulHeight_pair (x:Fin 2→K) (hx:x≠0) :
    Height.mulHeight x=infinitePair (x 0) (x 1)*finitePair (x 0) (x 1) := by
  rw [NumberField.mulHeight_eq hx]
  simp only [iSup_fin_two,infinitePair,finitePair]

lemma infinitePair_nonneg (a b:K) : 0 ≤ infinitePair a b := by
  apply Finset.prod_nonneg
  intro w _
  exact pow_nonneg ((apply_nonneg w a).trans (le_max_left _ _)) _

lemma finitePair_nonneg (a b:K) : 0≤finitePair a b :=
  finprod_nonneg (fun w=>(apply_nonneg w a).trans (le_max_left _ _))

lemma forms_ne_zero (Q:E.Point) : forms Q≠0 := by
  obtain ⟨s,hs,he⟩:=forms_represent_double Q
  rw [he]
  exact smul_ne_zero hs ((2:ℤ) • Q).xRep_ne_zero

/-- The homogeneous doubling forms have actual relative multiplicative
height between H(Q)^4/392² and676²H(Q)^4, at every point including torsion. -/
theorem multiplicative_bounds (Q:E.Point) :
    Height.mulHeight Q.xRep^4/(392:ℝ)^2≤Height.mulHeight (forms Q) ∧
    Height.mulHeight (forms Q)≤(676:ℝ)^2*Height.mulHeight Q.xRep^4 := by
  have hf:=finite_forms_bounds Q
  have hi:=infinite_forms_bounds (Q.xRep 0) (Q.xRep 1)
  have hp:=infinitePair_nonneg (Q.xRep 0) (Q.xRep 1)
  have hq:=finitePair_nonneg (F (Q.xRep 0) (Q.xRep 1)) (G (Q.xRep 0) (Q.xRep 1))
  have hlo:=mul_le_mul hi.1 hf.1 (by positivity) (infinitePair_nonneg _ _)
  have hup:=mul_le_mul hi.2 hf.2 hq (by positivity)
  rw [mulHeight_pair _ Q.xRep_ne_zero,mulHeight_pair _ (forms_ne_zero Q)]
  simp only [forms,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  constructor
  · convert hlo using 1 <;> ring
  · convert hup using 1 <;> ring

/-- Exact relative logarithmic duplication bounds, using the actual
number-field product formula and actual elliptic group operation. -/
theorem relative_bounds (Q:E.Point) :
    4*relativeXHeight Q-2*Real.log 392≤relativeXHeight ((2:ℤ) • Q) ∧
    relativeXHeight ((2:ℤ) • Q)≤4*relativeXHeight Q+2*Real.log 676 := by
  have hh:=multiplicative_bounds Q
  have hp:=Height.mulHeight_pos Q.xRep
  have hq:=Height.mulHeight_pos (forms Q)
  have hlo:=Real.log_le_log (show 0<Height.mulHeight Q.xRep^4/(392:ℝ)^2 by positivity) hh.1
  have hup:=Real.log_le_log hq hh.2
  rw [Real.log_div (by positivity) (by norm_num),Real.log_pow,Real.log_pow] at hlo
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow] at hup
  norm_num only [Nat.cast_ofNat] at hlo hup
  rw [double_height_forms]
  simp only [relativeXHeight,Height.logHeight_eq_log_mulHeight]
  constructor <;> linarith

lemma relative_height_element (Q:E.Point) :
    relativeXHeight Q=Height.logHeight₁ (Q.xRep 0) := by
  cases Q with
  | zero => simp [relativeXHeight,Point.xRep]
  | some x y h => simpa [relativeXHeight] using (Height.logHeight₁_eq_logHeight x).symm

lemma absolute_height_eq_half_relative (Q:E.Point) :
    GlobalSaturationHeight318.xHeight Q=relativeXHeight Q/2 := by
  rw [GlobalSaturationHeight318.xHeight,AbsoluteHeightNormalization318.absLogHeight_eq_half_relative,
    relative_height_element,Height.logHeight₁_eq_log_mulHeight₁]

/-- The precise unconditional absolute x-height estimate required for
canonical height construction. No detached height model or local premise remains. -/
theorem absolute_duplication_bounds (Q:E.Point) :
    4*GlobalSaturationHeight318.xHeight Q-Real.log 392≤GlobalSaturationHeight318.xHeight ((2:ℤ) • Q) ∧
    GlobalSaturationHeight318.xHeight ((2:ℤ) • Q)≤4*GlobalSaturationHeight318.xHeight Q+Real.log 676 := by
  have hh:=relative_bounds Q
  simp only [absolute_height_eq_half_relative]
  constructor <;> linarith

#print axioms absolute_duplication_bounds
end
end GlobalDuplicationHeight318
