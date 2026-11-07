module
public import AlternateSourceData318
public import SourcePrimarySplitLog318
public section
namespace ContactLeafData318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay RawDetector318 SourceContact318 RawLucasOrientation318
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

@[expose] def comparisonLeaf (S:ℚ) (w:Assignment) : Fin 4→K :=
  ![leaf10 S w,leaf11 S w,leaf12 S w,leaf13 S w]
@[expose] def comparison (S:ℚ) (w:Assignment) : Fin 4→K :=
  ![test10 S w,test11 S w,test12 S w,test13 S w]
@[expose] def comparisonDepth (j:Fin 4) : ℤ := if j=0 then 4 else 13
@[expose] def beta (w:Assignment) : ℚ := 3723+14892*w 0+14892*w 118
@[expose] def lucas (w:Assignment) : K :=
  (L3 w)^2-L2 w*(L2 w-2)*L3 w*L4 w+(L2 w-2)^2*(L4 w)^2-1

theorem comparison_eq (S:ℚ) (w:Assignment) (j:Fin 4) :
    comparison S w j=PrimaryFormal318.ratio w j-conj (AlternateSourceData318.rawRatio w j) := by
  fin_cases j <;> ext <;> norm_num [comparison,PrimaryFormal318.ratio,AlternateSourceData318.rawRatio,
    test10,test11,test12,test13,L1,L2,L3,L4,RawAlternatePade318.rawRatio1,
    RawAlternatePade318.rawRatio2,RawAlternatePade318.rawRatio3,RawAlternatePade318.rawRatio4,conj,pair] <;> ring

theorem comparison_square (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) (j:Fin 4) :
    comparisonLeaf S w j=(comparison S w j)^2 := by
  fin_cases j <;> simp only [comparisonLeaf,comparison,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact leaf10_square S w source
  · exact leaf11_square S w source
  · exact leaf12_square S w source
  · exact leaf13_square S w source

theorem beta_test (S:ℚ) (w:Assignment) : test14 S w=L1 w-pair (beta w) 0 := by
  ext <;> norm_num [test14,L1,beta,pair] <;> ring

theorem square_depth (v:AddValuation K (WithTop ℤ)) (x:K) (k:ℤ)
    (h:((2*k:ℤ):WithTop ℤ)≤v (x^2)) : (k:WithTop ℤ)≤v x := by
  by_cases hx:x=0
  · simp [hx]
  obtain ⟨a,ha⟩:=WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx)
  have he:v (x^2)=((2*a:ℤ):WithTop ℤ) := by rw [v.map_pow,←ha]; norm_cast
  rw [he] at h
  have hh:2*k≤2*a:=WithTop.coe_le_coe.mp h
  rw [←ha]
  exact WithTop.coe_le_coe.mpr (by omega)

/-- Literal weighted source leaves before square-depth extraction. -/
@[expose] def LeafBounds (v:AddValuation K (WithTop ℤ)) (S:ℚ) (w:Assignment) : Prop :=
  (8:WithTop ℤ)≤v (leaf0 S w) ∧ (2:WithTop ℤ)≤v (leaf5 S w) ∧
  (∀j,(2:WithTop ℤ)≤v (PrimaryFormal318.leaf S w j)) ∧
  (∀j,(2:WithTop ℤ)≤v (AlternateFormal318.leaf S w j)) ∧
  (∀j,((2*comparisonDepth j:ℤ):WithTop ℤ)≤v (comparisonLeaf S w j)) ∧
  (8:WithTop ℤ)≤v (leaf14 S w) ∧ (26:WithTop ℤ)≤v (leaf15 S w)

theorem source_tests (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (v:AddValuation K (WithTop ℤ)) (hb:LeafBounds v S w) :
    (∀j,(comparisonDepth j:WithTop ℤ)≤v (PrimaryFormal318.ratio w j-conj (AlternateSourceData318.rawRatio w j))) ∧
    (4:WithTop ℤ)≤v (L1 w-pair (beta w) 0) ∧ (13:WithTop ℤ)≤v (lucas w) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    rw [←comparison_eq S w j]
    exact square_depth v _ _ (by rw [←comparison_square S w source j]; exact hb.2.2.2.2.1 j)
  · rw [←beta_test S w]
    exact square_depth v _ 4 (by rw [←leaf14_square S w source]; exact hb.2.2.2.2.2.1)
  · change (13:WithTop ℤ)≤v ((L3 w)^2-L2 w*(L2 w-2)*L3 w*L4 w+(L2 w-2)^2*(L4 w)^2-1)
    rw [←lucas_actual S w source]
    exact square_depth v _ 13 (by rw [←leaf15_square S w source]; exact hb.2.2.2.2.2.2)

theorem inputs0_bounds (v:AddValuation K (WithTop ℤ)) (S:ℚ) (w:Assignment)
    (hb:∀x∈inputs0 S w,(2*x.2.2:ℤ)≤v x.2.1) : LeafBounds v S w := by
  refine ⟨?_,?_,PrimaryFormal318.inputs0_primary v S w hb,?_,?_,?_,?_⟩
  · exact hb (q0_4 S w,leaf0 S w,4) (by simp [inputs0])
  · exact hb (q0_1 S w,leaf5 S w,1) (by simp [inputs0])
  · intro j
    fin_cases j <;> simp only [AlternateFormal318.leaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
    · exact hb (q0_1 S w,leaf6 S w,1) (by simp [inputs0])
    · exact hb (q0_1 S w,leaf7 S w,1) (by simp [inputs0])
    · exact hb (q0_1 S w,leaf8 S w,1) (by simp [inputs0])
    · exact hb (q0_1 S w,leaf9 S w,1) (by simp [inputs0])
  · intro j
    fin_cases j <;> simp only [comparisonDepth,comparisonLeaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
    · simpa using hb (q0_4 S w,leaf10 S w,4) (by simp [inputs0])
    · simpa using hb (q0_13 S w,leaf11 S w,13) (by simp [inputs0])
    · simpa using hb (q0_13 S w,leaf12 S w,13) (by simp [inputs0])
    · simpa using hb (q0_13 S w,leaf13 S w,13) (by simp [inputs0])
  · exact hb (q0_4 S w,leaf14 S w,4) (by simp [inputs0])
  · exact hb (q0_13 S w,leaf15 S w,13) (by simp [inputs0])

theorem inputs1_bounds (v:AddValuation K (WithTop ℤ)) (S:ℚ) (w:Assignment)
    (hb:∀x∈inputs1 S w,(2*x.2.2:ℤ)≤v x.2.1) : LeafBounds v S w := by
  refine ⟨?_,?_,PrimaryFormal318.inputs1_primary v S w hb,?_,?_,?_,?_⟩
  · exact hb (q1_4 S w,leaf0 S w,4) (by simp [inputs1])
  · exact hb (q1_1 S w,leaf5 S w,1) (by simp [inputs1])
  · intro j
    fin_cases j <;> simp only [AlternateFormal318.leaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
    · exact hb (q1_1 S w,leaf6 S w,1) (by simp [inputs1])
    · exact hb (q1_1 S w,leaf7 S w,1) (by simp [inputs1])
    · exact hb (q1_1 S w,leaf8 S w,1) (by simp [inputs1])
    · exact hb (q1_1 S w,leaf9 S w,1) (by simp [inputs1])
  · intro j
    fin_cases j <;> simp only [comparisonDepth,comparisonLeaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
    · simpa using hb (q1_4 S w,leaf10 S w,4) (by simp [inputs1])
    · simpa using hb (q1_13 S w,leaf11 S w,13) (by simp [inputs1])
    · simpa using hb (q1_13 S w,leaf12 S w,13) (by simp [inputs1])
    · simpa using hb (q1_13 S w,leaf13 S w,13) (by simp [inputs1])
  · exact hb (q1_4 S w,leaf14 S w,4) (by simp [inputs1])
  · exact hb (q1_13 S w,leaf15 S w,13) (by simp [inputs1])

theorem inputs2_bounds (v:AddValuation K (WithTop ℤ)) (S:ℚ) (w:Assignment)
    (hb:∀x∈inputs2 S w,(2*x.2.2:ℤ)≤v x.2.1) : LeafBounds v S w := by
  refine ⟨?_,?_,PrimaryFormal318.inputs2_primary v S w hb,?_,?_,?_,?_⟩
  · exact hb (q2_4 S w,leaf0 S w,4) (by simp [inputs2])
  · exact hb (q2_1 S w,leaf5 S w,1) (by simp [inputs2])
  · intro j
    fin_cases j <;> simp only [AlternateFormal318.leaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
    · exact hb (q2_1 S w,leaf6 S w,1) (by simp [inputs2])
    · exact hb (q2_1 S w,leaf7 S w,1) (by simp [inputs2])
    · exact hb (q2_1 S w,leaf8 S w,1) (by simp [inputs2])
    · exact hb (q2_1 S w,leaf9 S w,1) (by simp [inputs2])
  · intro j
    fin_cases j <;> simp only [comparisonDepth,comparisonLeaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
    · simpa using hb (q2_4 S w,leaf10 S w,4) (by simp [inputs2])
    · simpa using hb (q2_13 S w,leaf11 S w,13) (by simp [inputs2])
    · simpa using hb (q2_13 S w,leaf12 S w,13) (by simp [inputs2])
    · simpa using hb (q2_13 S w,leaf13 S w,13) (by simp [inputs2])
  · exact hb (q2_4 S w,leaf14 S w,4) (by simp [inputs2])
  · exact hb (q2_13 S w,leaf15 S w,13) (by simp [inputs2])

end ContactLeafData318
#print axioms ContactLeafData318.source_tests
#print axioms ContactLeafData318.inputs0_bounds
