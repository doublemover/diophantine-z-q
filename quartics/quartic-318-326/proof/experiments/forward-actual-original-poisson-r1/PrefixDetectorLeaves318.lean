module
public import AllSelectedChartDepths318
public import RawDetector318
public section
noncomputable section
namespace PrefixDetectorLeaves318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain RawDetector318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! The original leaf identities need only already CONSTRUCTED prefix rows,
not a solution of all288 source equations. The algebraic proofs below retain
the literal source formulas and only narrow the row-domain requirement. -/
theorem leaf0_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf0 S w=(test0 S w)^2 := by
  have hr87 : r87 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=87) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg126 : w 126=((1 : ℚ)*(w 37)*(w 37)) := by dsimp only [r87] at hr87; linear_combination hr87
  dsimp only [leaf0,test0]
  rw [hg126]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf1_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf1 S w=(test1 S w)^2 := by
  have hr0 : r0 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=0) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg58 : w 58=((1 : ℚ)*(w 1)*(w 1) + (2 : ℚ)*(w 2)*(w 2)) := by dsimp only [r0] at hr0; linear_combination hr0
  have hr1 : r1 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=1) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg59 : w 59=((1 : ℚ)*(w 1)*(w 2)) := by dsimp only [r1] at hr1; linear_combination hr1
  dsimp only [leaf1,test1]
  rw [hg58,hg59]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf2_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf2 S w=(test2 S w)^2 := by
  have hr4 : r4 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=4) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg60 : w 60=((1 : ℚ)*(w 5)*(w 5) + (2 : ℚ)*(w 6)*(w 6)) := by dsimp only [r4] at hr4; linear_combination hr4
  have hr5 : r5 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=5) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg61 : w 61=((1 : ℚ)*(w 5)*(w 6)) := by dsimp only [r5] at hr5; linear_combination hr5
  dsimp only [leaf2,test2]
  rw [hg60,hg61]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf3_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf3 S w=(test3 S w)^2 := by
  have hr8 : r8 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=8) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg62 : w 62=((1 : ℚ)*(w 10)*(w 10) + (1 / 2 : ℚ)*(w 9)*(w 9)) := by dsimp only [r8] at hr8; linear_combination hr8
  have hr9 : r9 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=9) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg63 : w 63=((1 : ℚ)*(w 9)*(w 10)) := by dsimp only [r9] at hr9; linear_combination hr9
  dsimp only [leaf3,test3]
  rw [hg62,hg63]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf4_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf4 S w=(test4 S w)^2 := by
  have hr12 : r12 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=12) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg64 : w 64=((1 : ℚ)*(w 13)*(w 13) + (2 : ℚ)*(w 14)*(w 14)) := by dsimp only [r12] at hr12; linear_combination hr12
  have hr13 : r13 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=13) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg65 : w 65=((1 : ℚ)*(w 13)*(w 14)) := by dsimp only [r13] at hr13; linear_combination hr13
  dsimp only [leaf4,test4]
  rw [hg64,hg65]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf5_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf5 S w=(test5 S w)^2 := by
  have hr86 : r86 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=86) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg125 : w 125=((1 : ℚ)*(w 90)*(w 90) + (-8 : ℚ)*(w 91)*(w 91)) := by dsimp only [r86] at hr86; linear_combination hr86
  have hr51 : r51 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=51) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg90 : w 90=((1 : ℚ)*(w 76)*(w 76) + (2 : ℚ)*(w 77)*(w 77)) := by dsimp only [r51] at hr51; linear_combination hr51
  have hr52 : r52 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=52) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg91 : w 91=((1 : ℚ)*(w 76)*(w 77)) := by dsimp only [r52] at hr52; linear_combination hr52
  dsimp only [leaf5,test5]
  rw [hg125,hg90,hg91]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf10_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf10 S w=(test10 S w)^2 := by
  have hr88 : r88 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=88) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg127 : w 127=((1 : ℚ)*(w 102)*(w 102) + (-2 : ℚ)*(w 102)*(w 104) + (2 : ℚ)*(w 103)*(w 103) + (4 : ℚ)*(w 103)*(w 105) + (1 : ℚ)*(w 104)*(w 104) + (2 : ℚ)*(w 105)*(w 105)) := by dsimp only [r88] at hr88; linear_combination hr88
  have hr89 : r89 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=89) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg128 : w 128=((1 : ℚ)*(w 102)*(w 103) + (1 : ℚ)*(w 102)*(w 105) + (-1 : ℚ)*(w 103)*(w 104) + (-1 : ℚ)*(w 104)*(w 105)) := by dsimp only [r89] at hr89; linear_combination hr89
  dsimp only [leaf10,test10]
  rw [hg127,hg128]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf11_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf11 S w=(test11 S w)^2 := by
  have hr90 : r90 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=90) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg129 : w 129=((1 : ℚ)*(w 106)*(w 106) + (-2 : ℚ)*(w 106)*(w 108) + (2 : ℚ)*(w 107)*(w 107) + (4 : ℚ)*(w 107)*(w 109) + (1 : ℚ)*(w 108)*(w 108) + (2 : ℚ)*(w 109)*(w 109)) := by dsimp only [r90] at hr90; linear_combination hr90
  have hr91 : r91 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=91) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg130 : w 130=((1 : ℚ)*(w 106)*(w 107) + (1 : ℚ)*(w 106)*(w 109) + (-1 : ℚ)*(w 107)*(w 108) + (-1 : ℚ)*(w 108)*(w 109)) := by dsimp only [r91] at hr91; linear_combination hr91
  dsimp only [leaf11,test11]
  rw [hg129,hg130]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf12_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf12 S w=(test12 S w)^2 := by
  have hr92 : r92 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=92) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg131 : w 131=((1 : ℚ)*(w 110)*(w 110) + (-2 : ℚ)*(w 110)*(w 112) + (2 : ℚ)*(w 111)*(w 111) + (4 : ℚ)*(w 111)*(w 113) + (1 : ℚ)*(w 112)*(w 112) + (2 : ℚ)*(w 113)*(w 113)) := by dsimp only [r92] at hr92; linear_combination hr92
  have hr93 : r93 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=93) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg132 : w 132=((1 : ℚ)*(w 110)*(w 111) + (1 : ℚ)*(w 110)*(w 113) + (-1 : ℚ)*(w 111)*(w 112) + (-1 : ℚ)*(w 112)*(w 113)) := by dsimp only [r93] at hr93; linear_combination hr93
  dsimp only [leaf12,test12]
  rw [hg131,hg132]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf13_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf13 S w=(test13 S w)^2 := by
  have hr94 : r94 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=94) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg133 : w 133=((1 : ℚ)*(w 114)*(w 114) + (-2 : ℚ)*(w 114)*(w 116) + (2 : ℚ)*(w 115)*(w 115) + (4 : ℚ)*(w 115)*(w 117) + (1 : ℚ)*(w 116)*(w 116) + (2 : ℚ)*(w 117)*(w 117)) := by dsimp only [r94] at hr94; linear_combination hr94
  have hr95 : r95 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=95) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg134 : w 134=((1 : ℚ)*(w 114)*(w 115) + (1 : ℚ)*(w 114)*(w 117) + (-1 : ℚ)*(w 115)*(w 116) + (-1 : ℚ)*(w 116)*(w 117)) := by dsimp only [r95] at hr95; linear_combination hr95
  dsimp only [leaf13,test13]
  rw [hg133,hg134]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf14_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf14 S w=(test14 S w)^2 := by
  have hr96 : r96 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=96) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg135 : w 135=((1 : ℚ)*(w 0)*(w 0) + (-1 / 7446 : ℚ)*(w 0)*(w 102) + (2 : ℚ)*(w 0)*(w 118) + (1 / 221771664 : ℚ)*(w 102)*(w 102) + (-1 / 7446 : ℚ)*(w 102)*(w 118) + (1 / 110885832 : ℚ)*(w 103)*(w 103) + (1 : ℚ)*(w 118)*(w 118)) := by dsimp only [r96] at hr96; linear_combination hr96
  have hr97 : r97 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=97) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg136 : w 136=((1 : ℚ)*(w 0)*(w 103) + (-1 / 14892 : ℚ)*(w 102)*(w 103) + (1 : ℚ)*(w 103)*(w 118)) := by dsimp only [r97] at hr97; linear_combination hr97
  dsimp only [leaf14,test14]
  rw [hg135,hg136]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem leaf15_square (S : ℚ) (w : Assignment) (source : Constraints ((stage0 S).take 107) w) :
    leaf15 S w=(test15 S w)^2 := by
  have hr98 : r98 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=98) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg137 : w 137=((1 : ℚ)*(w 123)*(w 123) + (8 : ℚ)*(w 124)*(w 124)) := by dsimp only [r98] at hr98; linear_combination hr98
  have hr99 : r99 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=99) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hg138 : w 138=((1 : ℚ)*(w 123)*(w 124)) := by dsimp only [r99] at hr99; linear_combination hr99
  dsimp only [leaf15,test15]
  rw [hg137,hg138]
  ext <;> norm_num [pair,pow_two] <;> ring

theorem VA_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) :
    (pair (w 19) (-w 20))^2=1-pair 11 (6)*(pair (w 17) (-w 18))^4 := by
  have h16 : r16 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=16) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h17 : r17 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=17) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h18 : r18 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=18) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h19 : r19 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=19) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 66=(w 17)^2+2*(w 18)^2 := by dsimp only [r16] at h16; nlinarith
  have himag : w 67=w 17*w 18 := by dsimp only [r17] at h17; nlinarith
  dsimp only [r18] at h18
  dsimp only [r19] at h19
  rw [hreal,himag] at h18 h19
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h18
  · linear_combination -1*h19

theorem VA_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 19-1) (-w 20)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 17) (-w 18)) (pair (w 19) (-w 20)) hD h2
    (VA_curve_conjugate S w source)
  have hid : pair (w 19) (-w 20)-1=pair (w 19-1) (-w 20) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

theorem VS_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) :
    (pair (w 23) (-w 24))^2=1-pair 11 (6)*(pair (w 21) (-w 22))^4 := by
  have h20 : r20 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=20) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h21 : r21 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=21) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h22 : r22 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=22) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h23 : r23 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=23) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 68=(w 21)^2+2*(w 22)^2 := by dsimp only [r20] at h20; nlinarith
  have himag : w 69=w 21*w 22 := by dsimp only [r21] at h21; nlinarith
  dsimp only [r22] at h22
  dsimp only [r23] at h23
  rw [hreal,himag] at h22 h23
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h22
  · linear_combination -1*h23

theorem VS_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 23-1) (-w 24)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 21) (-w 22)) (pair (w 23) (-w 24)) hD h2
    (VS_curve_conjugate S w source)
  have hid : pair (w 23) (-w 24)-1=pair (w 23-1) (-w 24) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

theorem VT_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) :
    (pair (w 27) (-w 28))^2=1-pair 11 (6)*(pair (w 25) (-w 26))^4 := by
  have h24 : r24 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=24) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h25 : r25 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=25) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h26 : r26 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=26) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h27 : r27 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=27) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 70=(w 25)^2+2*(w 26)^2 := by dsimp only [r24] at h24; nlinarith
  have himag : w 71=w 25*w 26 := by dsimp only [r25] at h25; nlinarith
  dsimp only [r26] at h26
  dsimp only [r27] at h27
  rw [hreal,himag] at h26 h27
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h26
  · linear_combination -1*h27

theorem VT_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 27-1) (-w 28)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 25) (-w 26)) (pair (w 27) (-w 28)) hD h2
    (VT_curve_conjugate S w source)
  have hid : pair (w 27) (-w 28)-1=pair (w 27-1) (-w 28) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

theorem VZ_curve_conjugate (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) :
    (pair (w 31) (-w 32))^2=1-pair 11 (6)*(pair (w 29) (-w 30))^4 := by
  have h28 : r28 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=28) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h29 : r29 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=29) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h30 : r30 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=30) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have h31 : r31 S w=0 := source _ (List.getElem_mem (l:=(stage0 S).take 107) (n:=31) (by simp only [List.length_take,stage0,List.length_cons,List.length_nil]; decide))
  have hreal : w 72=(w 29)^2+2*(w 30)^2 := by dsimp only [r28] at h28; nlinarith
  have himag : w 73=w 29*w 30 := by dsimp only [r29] at h29; nlinarith
  dsimp only [r30] at h30
  dsimp only [r31] at h31
  rw [hreal,himag] at h30 h31
  ext <;> norm_num [pair,pow_succ]
  · linear_combination h30
  · linear_combination -1*h31

theorem VZ_linear_leaf_even (S : ℚ) (w : Assignment)
    (source : Constraints ((stage0 S).take 107) w) (v : AddValuation K (WithTop ℤ))
    (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (pair (w 31-1) (-w 32)) := by
  have hh := ValuationEvenNormChain.delta_even v (pair 11 6)
    (pair (w 29) (-w 30)) (pair (w 31) (-w 32)) hD h2
    (VZ_curve_conjugate S w source)
  have hid : pair (w 31) (-w 32)-1=pair (w 31-1) (-w 32) := by
    ext <;> simp [pair]
  simpa only [hid] using hh

end PrefixDetectorLeaves318
