module
public import Raw318FinalReplayData
public import ConcreteG8Domain
public import ValuationEvenNormChain
public section
namespace RawReciprocal318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open scoped QuadraticAlgebra
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! The four actual unsquared alternate delta leaves have intrinsic even
valuation. Each theorem consumes the literal source, including its CSE gates. -/
theorem VA_curve (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 19) (w 20))^2=1-pair 11 (-6)*(pair (w 17) (w 18))^4 := by
  have h16 : r16 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=16) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h17 : r17 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=17) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h18 : r18 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=18) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h19 : r19 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=19) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 66=(w 17)^2+2*(w 18)^2 := by dsimp only [r16] at h16; nlinarith
  have himag : w 67=w 17*w 18 := by dsimp only [r17] at h17; nlinarith
  dsimp only [r18] at h18
  dsimp only [r19] at h19
  rw [hreal,himag] at h18 h19
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h18
  · linear_combination 1*h19

theorem VA_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 19) (-w 20))^2=1-pair 11 (6)*(pair (w 17) (-w 18))^4 := by
  have h16 : r16 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=16) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h17 : r17 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=17) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h18 : r18 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=18) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h19 : r19 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=19) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 66=(w 17)^2+2*(w 18)^2 := by dsimp only [r16] at h16; nlinarith
  have himag : w 67=w 17*w 18 := by dsimp only [r17] at h17; nlinarith
  dsimp only [r18] at h18
  dsimp only [r19] at h19
  rw [hreal,himag] at h18 h19
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h18
  · linear_combination -1*h19

theorem VA_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 19-1) (-w 20)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 17) (-w 18)) (pair (w 19) (-w 20)) hD h2
    (VA_curve_conjugate S w source)
  have hid : pair (w 19) (-w 20)-1=pair (w 19-1) (-w 20) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

theorem VS_curve (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 23) (w 24))^2=1-pair 11 (-6)*(pair (w 21) (w 22))^4 := by
  have h20 : r20 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=20) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h21 : r21 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=21) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h22 : r22 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=22) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h23 : r23 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=23) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 68=(w 21)^2+2*(w 22)^2 := by dsimp only [r20] at h20; nlinarith
  have himag : w 69=w 21*w 22 := by dsimp only [r21] at h21; nlinarith
  dsimp only [r22] at h22
  dsimp only [r23] at h23
  rw [hreal,himag] at h22 h23
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h22
  · linear_combination 1*h23

theorem VS_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 23) (-w 24))^2=1-pair 11 (6)*(pair (w 21) (-w 22))^4 := by
  have h20 : r20 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=20) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h21 : r21 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=21) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h22 : r22 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=22) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h23 : r23 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=23) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 68=(w 21)^2+2*(w 22)^2 := by dsimp only [r20] at h20; nlinarith
  have himag : w 69=w 21*w 22 := by dsimp only [r21] at h21; nlinarith
  dsimp only [r22] at h22
  dsimp only [r23] at h23
  rw [hreal,himag] at h22 h23
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h22
  · linear_combination -1*h23

theorem VS_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 23-1) (-w 24)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 21) (-w 22)) (pair (w 23) (-w 24)) hD h2
    (VS_curve_conjugate S w source)
  have hid : pair (w 23) (-w 24)-1=pair (w 23-1) (-w 24) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

theorem VT_curve (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 27) (w 28))^2=1-pair 11 (-6)*(pair (w 25) (w 26))^4 := by
  have h24 : r24 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=24) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h25 : r25 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=25) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h26 : r26 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=26) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h27 : r27 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=27) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 70=(w 25)^2+2*(w 26)^2 := by dsimp only [r24] at h24; nlinarith
  have himag : w 71=w 25*w 26 := by dsimp only [r25] at h25; nlinarith
  dsimp only [r26] at h26
  dsimp only [r27] at h27
  rw [hreal,himag] at h26 h27
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h26
  · linear_combination 1*h27

theorem VT_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 27) (-w 28))^2=1-pair 11 (6)*(pair (w 25) (-w 26))^4 := by
  have h24 : r24 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=24) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h25 : r25 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=25) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h26 : r26 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=26) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h27 : r27 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=27) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 70=(w 25)^2+2*(w 26)^2 := by dsimp only [r24] at h24; nlinarith
  have himag : w 71=w 25*w 26 := by dsimp only [r25] at h25; nlinarith
  dsimp only [r26] at h26
  dsimp only [r27] at h27
  rw [hreal,himag] at h26 h27
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h26
  · linear_combination -1*h27

theorem VT_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 27-1) (-w 28)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 25) (-w 26)) (pair (w 27) (-w 28)) hD h2
    (VT_curve_conjugate S w source)
  have hid : pair (w 27) (-w 28)-1=pair (w 27-1) (-w 28) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

theorem VZ_curve (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 31) (w 32))^2=1-pair 11 (-6)*(pair (w 29) (w 30))^4 := by
  have h28 : r28 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=28) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h29 : r29 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=29) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h30 : r30 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=30) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h31 : r31 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=31) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 72=(w 29)^2+2*(w 30)^2 := by dsimp only [r28] at h28; nlinarith
  have himag : w 73=w 29*w 30 := by dsimp only [r29] at h29; nlinarith
  dsimp only [r30] at h30
  dsimp only [r31] at h31
  rw [hreal,himag] at h30 h31
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h30
  · linear_combination 1*h31

theorem VZ_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    (pair (w 31) (-w 32))^2=1-pair 11 (6)*(pair (w 29) (-w 30))^4 := by
  have h28 : r28 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=28) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h29 : r29 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=29) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h30 : r30 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=30) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h31 : r31 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=31) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 72=(w 29)^2+2*(w 30)^2 := by dsimp only [r28] at h28; nlinarith
  have himag : w 73=w 29*w 30 := by dsimp only [r29] at h29; nlinarith
  dsimp only [r30] at h30
  dsimp only [r31] at h31
  rw [hreal,himag] at h30 h31
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h30
  · linear_combination -1*h31

theorem VZ_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 31-1) (-w 32)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 29) (-w 30)) (pair (w 31) (-w 32)) hD h2
    (VZ_curve_conjugate S w source)
  have hid : pair (w 31) (-w 32)-1=pair (w 31-1) (-w 32) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

end RawReciprocal318
