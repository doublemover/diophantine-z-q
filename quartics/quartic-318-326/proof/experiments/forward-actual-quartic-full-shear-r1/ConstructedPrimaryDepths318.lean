module
public import SelectedActualChartLeaves318
public section
noncomputable section
namespace ConstructedPrimaryDepths318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain RawDetector318
open ConcretePadic318 ValuativeOrbitBounds318 DetectorWeightPreparation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

/-- These are the exact eight remaining original norm/comparison tests.
Their bounds are not claimed to follow from chart entry alone. -/
@[expose] def Remaining (v : AddValuation K (WithTop ℤ)) (w : Assignment) : Prop :=
  Bound v 4 (test0 0 w) ∧ Bound v 2 (test5 0 w) ∧
  Bound v 4 (test10 0 w) ∧ Bound v 13 (test11 0 w) ∧
  Bound v 13 (test12 0 w) ∧ Bound v 13 (test13 0 w) ∧
  Bound v 4 (test14 0 w) ∧ Bound v 13 (test15 0 w)

lemma positive_of_bound (v : AddValuation K (WithTop ℤ)) (x : K)
    (hx : Bound v 1 x) : 0<v x := lt_of_lt_of_le (by norm_num) hx

lemma weighted_square (v : AddValuation K (WithTop ℤ)) (q x : K) (m : ℤ)
    (hq : v q=(-(2*m-1):ℤ)) (hx : Bound v m x) : 0<v (q*x^2) := by
  have hq' : Bound v (-(2*m-1)) q := by rw [Bound,hq]
  exact positive_of_bound v _ (weaken v (bmul v hq' (bsquare v hx)) (by omega))

lemma weighted_linear (v : AddValuation K (WithTop ℤ)) (q x : K)
    (hq : v q=(-1:ℤ)) (hx : Bound v 4 x) : 0<v (q*x) := by
  have hq' : Bound v (-1) q := by rw [Bound,hq]
  exact positive_of_bound v _ (weaken v (bmul v hq' hx) (by norm_num))

/-- Actual sixteen primary weighted leaves from the constructed prefix,
four u-depths, four conjugated delta-depths, and the eight EXPLICIT remaining
norm/comparison estimates. No complete source solution is an input. -/
theorem all_positive (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (w : Assignment) (hw : Constraints ((stage0 0).take 107) w) (c t : ℚ)
    (hweights : rationalPlace p (weights c t 0)= -1 ∧
      rationalPlace p (weights c t 1)= -7 ∧ rationalPlace p (weights c t 2)= -25)
    (hu : ∀ j : Fin 4, Bound (place p rho hr) 4 (PadeRatioWitness318.u w (j.castAdd 4)))
    (hd : ∀ j : Fin 4, Bound (place p rho hr) 4 (SelectedActualChartLeaves318.linearLeaf w j))
    (hremaining : Remaining (place p rho hr) w) :
    ∀ a∈ActualDetectorFold318.leaves (ScaledDetectorChain318.view w c t),
      0<place p rho hr (a.1*a.2) := by
  let v := place p rho hr
  have hq0 : v (pair (weights c t 0) 0)=(-1:ℤ) := by simpa only [place_rational] using hweights.1
  have hq1 : v (pair (weights c t 1) 0)=(-7:ℤ) := by simpa only [place_rational] using hweights.2.1
  have hq2 : v (pair (weights c t 2) 0)=(-25:ℤ) := by simpa only [place_rational] using hweights.2.2
  obtain ⟨h0,h5,h10,h11,h12,h13,h14,h15⟩ := hremaining
  have pos0 : 0<v (pair (weights c t 1) 0*(pair (w 126) (0))) := by
    have hid : pair (w 126) (0)=leaf0 0 w := by
      ext <;> norm_num [leaf0,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf0_square 0 w hw]
    apply weighted_square v _ _ 4 hq1
    exact h0
  have pos5 : 0<v (pair (weights c t 0) 0*(pair (w 125) (0))) := by
    have hid : pair (w 125) (0)=leaf5 0 w := by
      ext <;> norm_num [leaf5,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf5_square 0 w hw]
    apply weighted_square v _ _ 1 hq0
    exact weaken v h5 (by norm_num)
  have pos1 : 0<v (pair (weights c t 0) 0*(pair (w 58) (2*w 59))) := by
    have hid : pair (w 58) (2*w 59)=leaf1 0 w := by
      ext <;> norm_num [leaf1,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf1_square 0 w hw]
    apply weighted_square v _ _ 1 hq0
    have he := weaken v (hu 0) (by norm_num : (1:ℤ)≤4)
    simpa only [test1,PadeRatioWitness318.u,one_mul] using he
  have pos2 : 0<v (pair (weights c t 0) 0*(pair (w 60) (2*w 61))) := by
    have hid : pair (w 60) (2*w 61)=leaf2 0 w := by
      ext <;> norm_num [leaf2,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf2_square 0 w hw]
    apply weighted_square v _ _ 1 hq0
    have he := weaken v (hu 1) (by norm_num : (1:ℤ)≤4)
    simpa only [test2,PadeRatioWitness318.u,one_mul] using he
  have pos3 : 0<v (pair (weights c t 0) 0*(pair (2*w 62) (2*w 63))) := by
    have hid : pair (2*w 62) (2*w 63)=leaf3 0 w := by
      ext <;> norm_num [leaf3,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf3_square 0 w hw]
    apply weighted_square v _ _ 1 hq0
    have he := weaken v (hu 2) (by norm_num : (1:ℤ)≤4)
    simpa only [test3,PadeRatioWitness318.u,one_mul] using he
  have pos4 : 0<v (pair (weights c t 0) 0*(pair (w 64) (2*w 65))) := by
    have hid : pair (w 64) (2*w 65)=leaf4 0 w := by
      ext <;> norm_num [leaf4,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf4_square 0 w hw]
    apply weighted_square v _ _ 1 hq0
    have he := weaken v (hu 3) (by norm_num : (1:ℤ)≤4)
    simpa only [test4,PadeRatioWitness318.u,one_mul] using he
  have pos6 : 0<v (pair (weights c t 0) 0*(pair (w 19-1) (-w 20))) := by
    apply weighted_linear v _ _ hq0
    simpa only [SelectedActualChartLeaves318.linearLeaf,PadeRatioWitness318.v,pair] using hd 0
  have pos7 : 0<v (pair (weights c t 0) 0*(pair (w 23-1) (-w 24))) := by
    apply weighted_linear v _ _ hq0
    simpa only [SelectedActualChartLeaves318.linearLeaf,PadeRatioWitness318.v,pair] using hd 1
  have pos8 : 0<v (pair (weights c t 0) 0*(pair (w 27-1) (-w 28))) := by
    apply weighted_linear v _ _ hq0
    simpa only [SelectedActualChartLeaves318.linearLeaf,PadeRatioWitness318.v,pair] using hd 2
  have pos9 : 0<v (pair (weights c t 0) 0*(pair (w 31-1) (-w 32))) := by
    apply weighted_linear v _ _ hq0
    simpa only [SelectedActualChartLeaves318.linearLeaf,PadeRatioWitness318.v,pair] using hd 3
  have pos10 : 0<v (pair (weights c t 1) 0*(pair (w 127) (2*w 128))) := by
    have hid : pair (w 127) (2*w 128)=leaf10 0 w := by
      ext <;> norm_num [leaf10,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf10_square 0 w hw]
    apply weighted_square v _ _ 4 hq1
    exact h10
  have pos11 : 0<v (pair (weights c t 2) 0*(pair (w 129) (2*w 130))) := by
    have hid : pair (w 129) (2*w 130)=leaf11 0 w := by
      ext <;> norm_num [leaf11,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf11_square 0 w hw]
    apply weighted_square v _ _ 13 hq2
    exact h11
  have pos12 : 0<v (pair (weights c t 2) 0*(pair (w 131) (2*w 132))) := by
    have hid : pair (w 131) (2*w 132)=leaf12 0 w := by
      ext <;> norm_num [leaf12,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf12_square 0 w hw]
    apply weighted_square v _ _ 13 hq2
    exact h12
  have pos13 : 0<v (pair (weights c t 2) 0*(pair (w 133) (2*w 134))) := by
    have hid : pair (w 133) (2*w 134)=leaf13 0 w := by
      ext <;> norm_num [leaf13,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf13_square 0 w hw]
    apply weighted_square v _ _ 13 hq2
    exact h13
  have pos14 : 0<v (pair (weights c t 1) 0*(pair (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729) (-7446*w 103-29784*w 136))) := by
    have hid : pair (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729) (-7446*w 103-29784*w 136)=leaf14 0 w := by
      ext <;> norm_num [leaf14,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf14_square 0 w hw]
    apply weighted_square v _ _ 4 hq1
    exact h14
  have pos15 : 0<v (pair (weights c t 2) 0*(pair (-2*w 123+w 137+1) (-4*w 124+4*w 138))) := by
    have hid : pair (-2*w 123+w 137+1) (-4*w 124+4*w 138)=leaf15 0 w := by
      ext <;> norm_num [leaf15,pair] <;> ring
    rw [hid,PrefixDetectorLeaves318.leaf15_square 0 w hw]
    apply weighted_square v _ _ 13 hq2
    exact h15
  intro a ha
  rw [leaves_weights] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  simp only [coefficients,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pos0
  · exact pos5
  · exact pos1
  · exact pos2
  · exact pos3
  · exact pos4
  · exact pos6
  · exact pos7
  · exact pos8
  · exact pos9
  · exact pos10
  · exact pos11
  · exact pos12
  · exact pos13
  · exact pos14
  · exact pos15

end ConstructedPrimaryDepths318
