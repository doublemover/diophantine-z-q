module
public import CoherentMultipleCharts318
public section
noncomputable section
namespace CoherentMultiplePrefix318
open ConcreteG8Domain (K)
open LocalGenerator318 (E P)
open CompressedGeneratorBridge318 (transport curve_eq transport_some)
open CoherentMultipleCharts318
open RealGuardTrace318 (guardValue)
set_option maxHeartbeats 1000000

/-- The first four actual nH charts, then the four actual n(H-P) charts.
The single integer h is shared by all eight; labels may be zero. -/
@[expose] def parameters (n : Fin 4 → ℤ) (h : ℤ) : Fin 8 → ℤ :=
  Fin.append (fun j => n j*h) (fun j => n j*(h-1))
@[expose] def u (n : Fin 4 → ℤ) (h : ℤ) : Fin 8 → K :=
  fun i => chartU (parameters n h i)
@[expose] def v (n : Fin 4 → ℤ) (h : ℤ) : Fin 8 → K :=
  fun i => chartV (parameters n h i)

theorem curves (n : Fin 4 → ℤ) (h : ℤ) (i : Fin 8) :
    (v n h i)^2=1-CompressedOrientation318.D*(u n h i)^4 :=
  chart_curve _

theorem left_point (n : Fin 4 → ℤ) (h : ℤ) (j : Fin 4) :
    transport curve_eq (PrimaryFormal318.point (u n h (j.castAdd 4)) (v n h (j.castAdd 4))
      (ReciprocalDifference318.ordinate_ne _ _ (curves n h _)) (curves n h _))=
      n j • (h • P) := by
  simpa only [u,v,parameters,Fin.append_left,←mul_zsmul] using chart_point (n j*h)

theorem right_point (n : Fin 4 → ℤ) (h : ℤ) (j : Fin 4) :
    transport curve_eq (PrimaryFormal318.point (u n h (j.natAdd 4)) (v n h (j.natAdd 4))
      (ReciprocalDifference318.ordinate_ne _ _ (curves n h _)) (curves n h _))=
      n j • (h • P-P) := by
  have he : h • P-P=(h-1) • P := by simp only [sub_eq_add_neg,add_zsmul,neg_one_zsmul]
  rw [he]
  simpa only [u,v,parameters,Fin.append_right,←mul_zsmul] using chart_point (n j*(h-1))

/-- The four literal real guards are exactly the actual arithmetic trace
values at the chosen common multiple, with no arbitrary chart assumptions. -/
theorem guards_iff (n : Fin 4 → ℤ) (h : ℤ) :
    RealGuardWitness318.Guards (u n h) ↔ ∀ j, guardValue (n j) (h • P)≠0 := by
  constructor <;> intro hg j
  · rw [←RealGuardTrace318.literal_guard (u n h) (v n h) j (n j) (h • P)
      (curves n h) (left_point n h j) (right_point n h j)]
    exact hg j
  · rw [RealGuardTrace318.literal_guard (u n h) (v n h) j (n j) (h • P)
      (curves n h) (left_point n h j) (right_point n h j)]
    exact hg j

/-- The concrete input-preserving assignment consumes exactly the nine
constructed charts. All unspecified entries retain the input placeholder. -/
@[expose] def witness (q : ℚ) (n : Fin 4 → ℤ) (h : ℤ) : CircuitReplay.Assignment :=
  RealGuardWitness318.fill (CompressedAnchorWitness318.fill
    (ReciprocalChartWitness318.fill (fun _ => q) (u n h) (v n h))
      (chartU h) (chartV h)) (u n h) (v n h)

@[simp] theorem witness_input (q : ℚ) (n : Fin 4 → ℤ) (h : ℤ) : witness q n h 0=q := by
  simp [witness]

theorem witness_rows (S q : ℚ) (n : Fin 4 → ℤ) (h : ℤ)
    (hh : h≠0) (hg : ∀ j, guardValue (n j) (h • P)≠0) :
    CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51) (witness q n h) :=
  RealGuardWitness318.first51_rows S (fun _ => q) (u n h) (v n h) (chartU h) (chartV h)
    (fun he => hh ((chartU_zero_iff h).mp he)) (curves n h) (chart_curve h)
    ((guards_iff n h).mpr hg)

/-- Actual integer-orbit specialization of the first51-row witness. Only the
four arithmetic guard values and h!=0 remain; all nine oriented charts are built. -/
theorem prefix_from_actual_guards (S q : ℚ) (n : Fin 4 → ℤ) (h : ℤ)
    (hh : h≠0) (hg : ∀ j, guardValue (n j) (h • P)≠0) :
    CircuitReplay.HasSolution ((Raw318FinalReplay.stage0 S).take 51) q := by
  exact ⟨witness q n h,witness_input q n h,witness_rows S q n h hh hg⟩

/-- At H=P, each nonzero-label trace is strictly negative. This supplies a
concrete nonempty prefix witness, not the large CRT-selected h needed later. -/
theorem guard_at_generator_negative (n : ℤ) (hn : n≠0) : guardValue n P<0 := by
  have hp := RealGuardTrace318.coefficient_pos (RealGuardTrace318.reciprocal (n • P))
    (RealGuardTrace318.reciprocal_multiple_positive ActualQuadraticEmbeddings318.positiveEmbedding n hn)
    (RealGuardTrace318.reciprocal_multiple_positive ActualQuadraticEmbeddings318.negativeEmbedding n hn)
  simpa [guardValue] using neg_neg_of_pos hp

/-- Unconditional witness existence for the literal first51 rows, preserving
arbitrary rational input. This deliberately says nothing about the remaining237 rows. -/
theorem prefix_hasSolution (S q : ℚ) :
    CircuitReplay.HasSolution ((Raw318FinalReplay.stage0 S).take 51) q := by
  apply prefix_from_actual_guards S q (fun _ => 1) 1 (by norm_num)
  intro j
  simpa only [one_zsmul] using (ne_of_lt (guard_at_generator_negative 1 (by norm_num)))

/-- Evaluation at the identity of the half-point orbit gives the historical
fixed signed square root candidate. Global constancy is a separate obligation. -/
theorem root_at_zero (n : Fin 4 → ℤ) (j : Fin 4) (hn : n j≠0) :
    RealGuardWitness318.root (u n 0) (v n 0) j= -(1/chartU (n j)) := by
  have hu : chartU (n j)≠0 := fun he => hn ((chartU_zero_iff _).mp he)
  simp only [RealGuardWitness318.root,RealGuardWitness318.numerator,
    RealGuardWitness318.denominator,u,v,parameters,Fin.append_left,Fin.append_right,
    mul_zero,zero_sub,mul_neg,mul_one,chartU_zero,chartV_zero,chartU_negative,
    chartV_negative,zero_mul,zero_add]
  field_simp [hu]
  ring

/-- Every guarded emitted root is an actual abscissa square root of the
fixed point n_j P. This does not yet identify its sign with fixedRoot. -/
theorem emitted_root_square (n : Fin 4 → ℤ) (h : ℤ) (j : Fin 4)
    (hg : (RealGuardWitness318.denominator (u n h) j).re≠0) :
    (RealGuardWitness318.root (u n h) (v n h) j)^2=(n j • P).xRep 0 := by
  obtain ⟨y,hy,he⟩ := RealGuardWitness318.actual_difference (u n h) (v n h) j (curves n h) hg
  have ht := congrArg (transport curve_eq) he
  rw [map_sub,left_point,right_point,transport_some,zsmul_sub,sub_sub_cancel] at ht
  rw [ht]
  simp only [WeierstrassCurve.Affine.Point.xRep_some,Matrix.cons_val_zero]

/-- The exact remaining ambiguity is a sign, not a new square root. -/
theorem emitted_root_eq_or_neg (n : Fin 4 → ℤ) (h : ℤ) (j : Fin 4)
    (hn : n j≠0) (hg : (RealGuardWitness318.denominator (u n h) j).re≠0) :
    RealGuardWitness318.root (u n h) (v n h) j=fixedRoot (n j) ∨
      RealGuardWitness318.root (u n h) (v n h) j= -fixedRoot (n j) :=
  sq_eq_sq_iff_eq_or_eq_neg.mp ((emitted_root_square n h j hg).trans
    (fixedRoot_square (n j) hn).symm)

end CoherentMultiplePrefix318
