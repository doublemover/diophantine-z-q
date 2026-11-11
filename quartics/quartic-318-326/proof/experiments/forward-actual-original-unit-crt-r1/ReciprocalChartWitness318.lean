module
public import CompressedAnchorWitness318
public section

/-! Forward assembly of all eight literal reciprocal chart blocks. -/
namespace ReciprocalChartWitness318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- Fill the 32 chart entries and their 16 actual square gates. The third
chart uses the emitted half-scaled real square gate, exactly as stored. -/
@[expose] def fill (base : Assignment) (u v : Fin 8 → K) : Assignment :=
  fun n => match n with
    | 1 => (u 0).re
    | 2 => (u 0).im
    | 3 => (v 0).re
    | 4 => (v 0).im
    | 5 => (u 1).re
    | 6 => (u 1).im
    | 7 => (v 1).re
    | 8 => (v 1).im
    | 9 => (u 2).re
    | 10 => (u 2).im
    | 11 => (v 2).re
    | 12 => (v 2).im
    | 13 => (u 3).re
    | 14 => (u 3).im
    | 15 => (v 3).re
    | 16 => (v 3).im
    | 17 => (u 4).re
    | 18 => (u 4).im
    | 19 => (v 4).re
    | 20 => (v 4).im
    | 21 => (u 5).re
    | 22 => (u 5).im
    | 23 => (v 5).re
    | 24 => (v 5).im
    | 25 => (u 6).re
    | 26 => (u 6).im
    | 27 => (v 6).re
    | 28 => (v 6).im
    | 29 => (u 7).re
    | 30 => (u 7).im
    | 31 => (v 7).re
    | 32 => (v 7).im
    | 58 => ((u 0)^2).re
    | 59 => (u 0).re*(u 0).im
    | 60 => ((u 1)^2).re
    | 61 => (u 1).re*(u 1).im
    | 62 => ((u 2)^2).re/2
    | 63 => (u 2).re*(u 2).im
    | 64 => ((u 3)^2).re
    | 65 => (u 3).re*(u 3).im
    | 66 => ((u 4)^2).re
    | 67 => (u 4).re*(u 4).im
    | 68 => ((u 5)^2).re
    | 69 => (u 5).re*(u 5).im
    | 70 => ((u 6)^2).re
    | 71 => (u 6).re*(u 6).im
    | 72 => ((u 7)^2).re
    | 73 => (u 7).re*(u 7).im
    | n => base n

@[simp] theorem fill_input (base : Assignment) (u v : Fin 8 → K) :
    fill base u v 0=base 0 := by simp [fill]

theorem chart0_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 0)^2=1-D*(u 0)^4) :
    r0 S (fill base u v)=0 ∧ r1 S (fill base u v)=0 ∧ r2 S (fill base u v)=0 ∧ r3 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r0,fill,pow_two]; ring
  constructor
  · simp [r1,fill]
  constructor
  · norm_num [r2,fill,pow_two]
    linear_combination hre
  · norm_num [r3,fill,pow_two]
    linear_combination him

theorem chart1_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 1)^2=1-D*(u 1)^4) :
    r4 S (fill base u v)=0 ∧ r5 S (fill base u v)=0 ∧ r6 S (fill base u v)=0 ∧ r7 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r4,fill,pow_two]; ring
  constructor
  · simp [r5,fill]
  constructor
  · norm_num [r6,fill,pow_two]
    linear_combination hre
  · norm_num [r7,fill,pow_two]
    linear_combination him

theorem chart2_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 2)^2=1-D*(u 2)^4) :
    r8 S (fill base u v)=0 ∧ r9 S (fill base u v)=0 ∧ r10 S (fill base u v)=0 ∧ r11 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r8,fill,pow_two]; ring
  constructor
  · simp [r9,fill]
  constructor
  · norm_num [r10,fill,pow_two]
    linear_combination hre
  · norm_num [r11,fill,pow_two]
    linear_combination him

theorem chart3_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 3)^2=1-D*(u 3)^4) :
    r12 S (fill base u v)=0 ∧ r13 S (fill base u v)=0 ∧ r14 S (fill base u v)=0 ∧ r15 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r12,fill,pow_two]; ring
  constructor
  · simp [r13,fill]
  constructor
  · norm_num [r14,fill,pow_two]
    linear_combination hre
  · norm_num [r15,fill,pow_two]
    linear_combination him

theorem chart4_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 4)^2=1-D*(u 4)^4) :
    r16 S (fill base u v)=0 ∧ r17 S (fill base u v)=0 ∧ r18 S (fill base u v)=0 ∧ r19 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r16,fill,pow_two]; ring
  constructor
  · simp [r17,fill]
  constructor
  · norm_num [r18,fill,pow_two]
    linear_combination hre
  · norm_num [r19,fill,pow_two]
    linear_combination him

theorem chart5_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 5)^2=1-D*(u 5)^4) :
    r20 S (fill base u v)=0 ∧ r21 S (fill base u v)=0 ∧ r22 S (fill base u v)=0 ∧ r23 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r20,fill,pow_two]; ring
  constructor
  · simp [r21,fill]
  constructor
  · norm_num [r22,fill,pow_two]
    linear_combination hre
  · norm_num [r23,fill,pow_two]
    linear_combination him

theorem chart6_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 6)^2=1-D*(u 6)^4) :
    r24 S (fill base u v)=0 ∧ r25 S (fill base u v)=0 ∧ r26 S (fill base u v)=0 ∧ r27 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r24,fill,pow_two]; ring
  constructor
  · simp [r25,fill]
  constructor
  · norm_num [r26,fill,pow_two]
    linear_combination hre
  · norm_num [r27,fill,pow_two]
    linear_combination him

theorem chart7_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : (v 7)^2=1-D*(u 7)^4) :
    r28 S (fill base u v)=0 ∧ r29 S (fill base u v)=0 ∧ r30 S (fill base u v)=0 ∧ r31 S (fill base u v)=0 := by
  have hre := congrArg QuadraticAlgebra.re hc
  have him := congrArg QuadraticAlgebra.im hc
  norm_num [D,pair,pow_succ] at hre him
  constructor
  · simp [r28,fill,pow_two]; ring
  constructor
  · simp [r29,fill]
  constructor
  · norm_num [r30,fill,pow_two]
    linear_combination hre
  · norm_num [r31,fill,pow_two]
    linear_combination him

/-- Exact source prefix, with no equations outside the prefix asserted. -/
@[expose] def rows (S : ℚ) : List Row :=
  [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S]

theorem rows_eq_prefix (S : ℚ) : rows S=(stage0 S).take 32 := by rfl

theorem literal_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (hc : ∀ j, (v j)^2=1-D*(u j)^4) : Constraints (rows S) (fill base u v) := by
  obtain ⟨h0,h1,h2,h3⟩ := chart0_rows S base u v (hc 0)
  obtain ⟨h4,h5,h6,h7⟩ := chart1_rows S base u v (hc 1)
  obtain ⟨h8,h9,h10,h11⟩ := chart2_rows S base u v (hc 2)
  obtain ⟨h12,h13,h14,h15⟩ := chart3_rows S base u v (hc 3)
  obtain ⟨h16,h17,h18,h19⟩ := chart4_rows S base u v (hc 4)
  obtain ⟨h20,h21,h22,h23⟩ := chart5_rows S base u v (hc 5)
  obtain ⟨h24,h25,h26,h27⟩ := chart6_rows S base u v (hc 6)
  obtain ⟨h28,h29,h30,h31⟩ := chart7_rows S base u v (hc 7)
  simp [Constraints,rows,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31]

/-- These 48 coordinates avoid every compressed-anchor coordinate. -/
theorem anchor_preserves_rows (S : ℚ) (base : Assignment) (uH vH : K)
    (hr : Constraints (rows S) base) :
    Constraints (rows S) (CompressedAnchorWitness318.fill base uH vH) := by
  simp only [Constraints,rows,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hr ⊢
  simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,CompressedAnchorWitness318.fill] using hr

/-- The first 39 actual rows are assembled in one compatible assignment.
The two chart families are prescribed by the caller; no simultaneous global
point choice or later source equation is assumed proved. -/
theorem first39_rows (S : ℚ) (base : Assignment) (u v : Fin 8 → K)
    (uH vH : K) (huH : uH≠0)
    (hc : ∀ j, (v j)^2=1-D*(u j)^4) (hH : vH^2=1-D*uH^4) :
    Constraints ((stage0 S).take 39)
      (CompressedAnchorWitness318.fill (fill base u v) uH vH) := by
  have hp := anchor_preserves_rows S (fill base u v) uH vH
    (literal_rows S base u v hc)
  obtain ⟨h32,h33,h34,h35,h36,h37,h38⟩ :=
    CompressedAnchorWitness318.literal_rows S (fill base u v) uH vH huH hH
  simp only [Constraints,rows,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hp
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31⟩ := hp
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S]
    (CompressedAnchorWitness318.fill (fill base u v) uH vH)
  simp [Constraints,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38]

/-- Input-preserving witness existence for exactly the checked prefix.
This is a finite assembly step; its chart hypotheses are not existentially
supplied by this theorem. -/
theorem prefix_hasSolution (S q : ℚ) (u v : Fin 8 → K) (uH vH : K)
    (huH : uH≠0) (hc : ∀ j, (v j)^2=1-D*(u j)^4)
    (hH : vH^2=1-D*uH^4) : HasSolution ((stage0 S).take 39) q := by
  refine ⟨CompressedAnchorWitness318.fill (fill (fun _ => q) u v) uH vH, ?_,
    first39_rows S (fun _ => q) u v uH vH huH hc hH⟩
  simp

#print axioms literal_rows
#print axioms anchor_preserves_rows
#print axioms first39_rows
#print axioms prefix_hasSolution
end
end ReciprocalChartWitness318
