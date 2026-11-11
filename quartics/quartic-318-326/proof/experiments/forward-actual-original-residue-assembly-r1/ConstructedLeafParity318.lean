module
public import PrefixDetectorLeaves318
public section
noncomputable section
namespace ConstructedLeafParity318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain RawDetector318
open ValuationEvenNormChain
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

/-- Opposite-place evenness holds for all sixteen ACTUAL leaf values from
only the constructed first107 rows. Four unsquared conjugated deltas use
the original curve equation; the other twelve are literal squares. -/
theorem all_even (S : ℚ) (w : Assignment)
    (hw : Constraints ((stage0 S).take 107) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0)
    (c t : ℚ) :
    ∀ a∈ActualDetectorFold318.leaves (ScaledDetectorChain318.view w c t), EvenAt v a.2 := by
  have h0 : EvenAt v (pair (w 126) (0)) := by
    have he := square_even v (test0 S w)
    rw [←PrefixDetectorLeaves318.leaf0_square S w hw] at he
    have hid : pair (w 126) (0)=leaf0 S w := by
      ext <;> norm_num [leaf0,pair] <;> ring
    rw [hid]
    exact he
  have h5 : EvenAt v (pair (w 125) (0)) := by
    have he := square_even v (test5 S w)
    rw [←PrefixDetectorLeaves318.leaf5_square S w hw] at he
    have hid : pair (w 125) (0)=leaf5 S w := by
      ext <;> norm_num [leaf5,pair] <;> ring
    rw [hid]
    exact he
  have h1 : EvenAt v (pair (w 58) (2*w 59)) := by
    have he := square_even v (test1 S w)
    rw [←PrefixDetectorLeaves318.leaf1_square S w hw] at he
    have hid : pair (w 58) (2*w 59)=leaf1 S w := by
      ext <;> norm_num [leaf1,pair] <;> ring
    rw [hid]
    exact he
  have hLeaf2 : EvenAt v (pair (w 60) (2*w 61)) := by
    have he := square_even v (test2 S w)
    rw [←PrefixDetectorLeaves318.leaf2_square S w hw] at he
    have hid : pair (w 60) (2*w 61)=leaf2 S w := by
      ext <;> norm_num [leaf2,pair] <;> ring
    rw [hid]
    exact he
  have h3 : EvenAt v (pair (2*w 62) (2*w 63)) := by
    have he := square_even v (test3 S w)
    rw [←PrefixDetectorLeaves318.leaf3_square S w hw] at he
    have hid : pair (2*w 62) (2*w 63)=leaf3 S w := by
      ext <;> norm_num [leaf3,pair] <;> ring
    rw [hid]
    exact he
  have h4 : EvenAt v (pair (w 64) (2*w 65)) := by
    have he := square_even v (test4 S w)
    rw [←PrefixDetectorLeaves318.leaf4_square S w hw] at he
    have hid : pair (w 64) (2*w 65)=leaf4 S w := by
      ext <;> norm_num [leaf4,pair] <;> ring
    rw [hid]
    exact he
  have h6 : EvenAt v (pair (w 19-1) (-w 20)) := by
    exact PrefixDetectorLeaves318.VA_linear_leaf_even S w hw v hD h2
  have h7 : EvenAt v (pair (w 23-1) (-w 24)) := by
    exact PrefixDetectorLeaves318.VS_linear_leaf_even S w hw v hD h2
  have h8 : EvenAt v (pair (w 27-1) (-w 28)) := by
    exact PrefixDetectorLeaves318.VT_linear_leaf_even S w hw v hD h2
  have h9 : EvenAt v (pair (w 31-1) (-w 32)) := by
    exact PrefixDetectorLeaves318.VZ_linear_leaf_even S w hw v hD h2
  have h10 : EvenAt v (pair (w 127) (2*w 128)) := by
    have he := square_even v (test10 S w)
    rw [←PrefixDetectorLeaves318.leaf10_square S w hw] at he
    have hid : pair (w 127) (2*w 128)=leaf10 S w := by
      ext <;> norm_num [leaf10,pair] <;> ring
    rw [hid]
    exact he
  have h11 : EvenAt v (pair (w 129) (2*w 130)) := by
    have he := square_even v (test11 S w)
    rw [←PrefixDetectorLeaves318.leaf11_square S w hw] at he
    have hid : pair (w 129) (2*w 130)=leaf11 S w := by
      ext <;> norm_num [leaf11,pair] <;> ring
    rw [hid]
    exact he
  have h12 : EvenAt v (pair (w 131) (2*w 132)) := by
    have he := square_even v (test12 S w)
    rw [←PrefixDetectorLeaves318.leaf12_square S w hw] at he
    have hid : pair (w 131) (2*w 132)=leaf12 S w := by
      ext <;> norm_num [leaf12,pair] <;> ring
    rw [hid]
    exact he
  have h13 : EvenAt v (pair (w 133) (2*w 134)) := by
    have he := square_even v (test13 S w)
    rw [←PrefixDetectorLeaves318.leaf13_square S w hw] at he
    have hid : pair (w 133) (2*w 134)=leaf13 S w := by
      ext <;> norm_num [leaf13,pair] <;> ring
    rw [hid]
    exact he
  have h14 : EvenAt v (pair (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729) (-7446*w 103-29784*w 136)) := by
    have he := square_even v (test14 S w)
    rw [←PrefixDetectorLeaves318.leaf14_square S w hw] at he
    have hid : pair (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729) (-7446*w 103-29784*w 136)=leaf14 S w := by
      ext <;> norm_num [leaf14,pair] <;> ring
    rw [hid]
    exact he
  have h15 : EvenAt v (pair (-2*w 123+w 137+1) (-4*w 124+4*w 138)) := by
    have he := square_even v (test15 S w)
    rw [←PrefixDetectorLeaves318.leaf15_square S w hw] at he
    have hid : pair (-2*w 123+w 137+1) (-4*w 124+4*w 138)=leaf15 S w := by
      ext <;> norm_num [leaf15,pair] <;> ring
    rw [hid]
    exact he
  intro a ha
  simp only [ActualDetectorFold318.leaves,ScaledDetectorChain318.view,
    ContactChainLimits318.view] at ha
  norm_num only at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h5
  · exact h1
  · exact hLeaf2
  · exact h3
  · exact h4
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- All three scaled views preserve the very same original source prefix.
No assumption that the source has a complete288-row solution is introduced. -/
theorem actual_even (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hzero : h≠0) (hone : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0)
    (c t : ℚ) :
    ∀ a∈ActualDetectorFold318.leaves
      (ScaledDetectorChain318.view (DetectorGateWitness318.witness q labels h) c t),
      EvenAt v a.2 :=
  all_even 0 _ (DetectorGateWitness318.witness_first107 0 q labels h hzero hone hg) v hD h2 c t

end ConstructedLeafParity318
