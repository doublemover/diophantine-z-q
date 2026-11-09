module
public import ReciprocalChartWitness318
public import ReciprocalDifference318
public section

/-! Conditional forward witnesses for the four literal real-part root guards.
The real-part nonvanishing hypotheses are explicit; this file does not choose
compatible global multiples or establish integer-to-source completeness. -/
namespace RealGuardWitness318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def denominator (u : Fin 8 → K) (j : Fin 4) : K :=
  (u (j.natAdd 4))^2-(u (j.castAdd 4))^2

@[expose] def numerator (u v : Fin 8 → K) (j : Fin 4) : K :=
  u (j.castAdd 4)*v (j.natAdd 4)+u (j.natAdd 4)*v (j.castAdd 4)

@[expose] def root (u v : Fin 8 → K) (j : Fin 4) : K :=
  numerator u v j / denominator u j

/-- This is the rational coefficient, not either real embedding. -/
@[expose] def Guards (u : Fin 8 → K) : Prop := ∀ j, (denominator u j).re≠0

theorem denominator_ne (u : Fin 8 → K) (j : Fin 4)
    (hg : (denominator u j).re≠0) : denominator u j≠0 := by
  intro he
  apply hg
  rw [he]
  rfl

theorem root_equation (u v : Fin 8 → K) (j : Fin 4)
    (hg : (denominator u j).re≠0) :
    denominator u j * root u v j = numerator u v j := by
  dsimp [root]
  field_simp [denominator_ne u j hg]

/-- Only the twelve emitted guard/root coordinates are replaced. -/
@[expose] def fill (base : Assignment) (u v : Fin 8 → K) : Assignment :=
  fun n => match n with
    | 78 => (denominator u 0).re⁻¹
    | 79 => (root u v 0).re
    | 80 => (root u v 0).im
    | 81 => (denominator u 1).re⁻¹
    | 82 => (root u v 1).re
    | 83 => (root u v 1).im
    | 84 => (denominator u 2).re⁻¹
    | 85 => (root u v 2).re
    | 86 => (root u v 2).im
    | 87 => (denominator u 3).re⁻¹
    | 88 => (root u v 3).re
    | 89 => (root u v 3).im
    | n => base n

@[simp] theorem fill_input (base : Assignment) (u v : Fin 8 → K) :
    fill base u v 0=base 0 := by simp [fill]

theorem fill_other (base : Assignment) (u v : Fin 8 → K) (n : ℕ)
    (hn : n<78 ∨ 90≤n) : fill base u v n=base n := by
  rcases hn with hn | hn <;> simp [fill,show n≠78 by omega,show n≠79 by omega,
    show n≠80 by omega,show n≠81 by omega,show n≠82 by omega,
    show n≠83 by omega,show n≠84 by omega,show n≠85 by omega,
    show n≠86 by omega,show n≠87 by omega,show n≠88 by omega,show n≠89 by omega]

theorem block0_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hg : (denominator u 0).re≠0) :
    r39 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r40 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r41 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 := by
  have hi := mul_inv_cancel₀ hg
  have hre := congrArg QuadraticAlgebra.re (root_equation u v 0 hg)
  have him := congrArg QuadraticAlgebra.im (root_equation u v 0 hg)
  norm_num [denominator,numerator,pow_succ] at hi hre him
  constructor
  · norm_num [r39,fill,ReciprocalChartWitness318.fill,denominator,pow_succ]
    linear_combination hi
  constructor
  · norm_num [r40,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination hre
  · norm_num [r41,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination him

theorem block1_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hg : (denominator u 1).re≠0) :
    r42 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r43 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r44 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 := by
  have hi := mul_inv_cancel₀ hg
  have hre := congrArg QuadraticAlgebra.re (root_equation u v 1 hg)
  have him := congrArg QuadraticAlgebra.im (root_equation u v 1 hg)
  norm_num [denominator,numerator,pow_succ] at hi hre him
  constructor
  · norm_num [r42,fill,ReciprocalChartWitness318.fill,denominator,pow_succ]
    linear_combination hi
  constructor
  · norm_num [r43,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination hre
  · norm_num [r44,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination him

theorem block2_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hg : (denominator u 2).re≠0) :
    r45 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r46 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r47 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 := by
  have hi := mul_inv_cancel₀ hg
  have hre := congrArg QuadraticAlgebra.re (root_equation u v 2 hg)
  have him := congrArg QuadraticAlgebra.im (root_equation u v 2 hg)
  norm_num [denominator,numerator,pow_succ] at hi hre him
  constructor
  · norm_num [r45,fill,ReciprocalChartWitness318.fill,denominator,pow_succ]
    linear_combination hi
  constructor
  · norm_num [r46,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination hre
  · norm_num [r47,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination him

theorem block3_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hg : (denominator u 3).re≠0) :
    r48 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r49 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 ∧
    r50 S (fill (ReciprocalChartWitness318.fill base u v) u v)=0 := by
  have hi := mul_inv_cancel₀ hg
  have hre := congrArg QuadraticAlgebra.re (root_equation u v 3 hg)
  have him := congrArg QuadraticAlgebra.im (root_equation u v 3 hg)
  norm_num [denominator,numerator,pow_succ] at hi hre him
  constructor
  · norm_num [r48,fill,ReciprocalChartWitness318.fill,denominator,pow_succ]
    linear_combination hi
  constructor
  · norm_num [r49,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination hre
  · norm_num [r50,fill,ReciprocalChartWitness318.fill,pow_succ]
    linear_combination him

/-- The literal list, not a replacement system. -/
@[expose] def rows (S : ℚ) : List Row :=
  [r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S]

theorem rows_eq_slice (S : ℚ) : rows S=((stage0 S).drop 39).take 12 := by rfl

theorem literal_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hg : Guards u) :
    Constraints (rows S) (fill (ReciprocalChartWitness318.fill base u v) u v) := by
  obtain ⟨h39,h40,h41⟩ := block0_rows S base u v (hg 0)
  obtain ⟨h42,h43,h44⟩ := block1_rows S base u v (hg 1)
  obtain ⟨h45,h46,h47⟩ := block2_rows S base u v (hg 2)
  obtain ⟨h48,h49,h50⟩ := block3_rows S base u v (hg 3)
  simp [Constraints,rows,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50]

/-- Later guard coordinates do not alter any of the first 39 rows. -/
theorem preserves_first39 (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (h : Constraints ((stage0 S).take 39) base) :
    Constraints ((stage0 S).take 39) (fill base u v) := by
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S] base at h
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S] (fill base u v)
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at h ⊢
  simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,fill] using h

/-- Inserting the anchor before the guard fill preserves every root row. -/
theorem anchor_preserves_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (uH vH : K) (h : Constraints (rows S) (fill base u v)) :
    Constraints (rows S) (fill (CompressedAnchorWitness318.fill base uH vH) u v) := by
  simp only [Constraints,rows,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at h ⊢
  simpa [r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,fill,CompressedAnchorWitness318.fill] using h

/-- One assignment for the 51 actual first rows. Four real-part guards and
nine compatible chart inputs are still explicit hypotheses. -/
theorem first51_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (uH vH : K) (huH : uH≠0) (hc : ∀ j, (v j)^2=1-D*(u j)^4)
    (hH : vH^2=1-D*uH^4) (hg : Guards u) :
    Constraints ((stage0 S).take 51)
      (fill (CompressedAnchorWitness318.fill (ReciprocalChartWitness318.fill base u v) uH vH) u v) := by
  change Constraints (((stage0 S).take 39) ++ rows S) _
  apply (constraints_append _ _ _).mpr
  constructor
  · exact preserves_first39 S _ u v (ReciprocalChartWitness318.first39_rows S base u v uH vH huH hc hH)
  · exact anchor_preserves_rows S _ u v uH vH (literal_rows S base u v hg)

/-- This conditional prefix construction accepts arbitrary rational input.
It does not assert the source solution required for integer completeness. -/
theorem prefix_hasSolution (S q : ℚ) (u v : Fin 8 → K) (uH vH : K)
    (huH : uH≠0) (hc : ∀ j, (v j)^2=1-D*(u j)^4)
    (hH : vH^2=1-D*uH^4) (hg : Guards u) :
    HasSolution ((stage0 S).take 51) q := by
  refine ⟨fill (CompressedAnchorWitness318.fill
    (ReciprocalChartWitness318.fill (fun _ => q) u v) uH vH) u v, ?_,
    first51_rows S (fun _ => q) u v uH vH huH hc hH hg⟩
  simp

/-- Conditional roots are the abscissae of the original oriented differences.
The reciprocal identity charts are included, because actual_difference includes
those cases. The stronger rational real-part guard supplies its K denominator. -/
theorem actual_difference (u v : Fin 8 → K) (j : Fin 4)
    (hc : ∀ i, (v i)^2=1-D*(u i)^4) (hg : (denominator u j).re≠0) :
    ∃ (y : K) (hn : CompressedPoint318.E.Nonsingular ((root u v j)^2) y),
      PrimaryFormal318.point (u (j.castAdd 4)) (v (j.castAdd 4))
        (ReciprocalDifference318.ordinate_ne _ _ (hc _)) (hc _) -
      PrimaryFormal318.point (u (j.natAdd 4)) (v (j.natAdd 4))
        (ReciprocalDifference318.ordinate_ne _ _ (hc _)) (hc _) =
      WeierstrassCurve.Affine.Point.some ((root u v j)^2) y hn := by
  exact ReciprocalDifference318.actual_difference _ _ _ _ _
    (hc _) (hc _) (denominator_ne u j hg) (root_equation u v j hg)

#print axioms root_equation
#print axioms first51_rows
#print axioms prefix_hasSolution
#print axioms actual_difference
end
end RealGuardWitness318
