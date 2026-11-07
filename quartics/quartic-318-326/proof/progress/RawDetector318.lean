module
public import RawReciprocal318
public import ConcreteValuationTrace
public section
namespace RawDetector318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open scoped QuadraticAlgebra
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! Literal decoding of every leaf and every actual detector-chain step.
The test order is deliberately 0,5,1,2,3,4,6,...,15. -/
@[expose] def leaf0 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 126)) (0 : ℚ))
@[expose] def test0 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 37)) (0 : ℚ))
theorem leaf0_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf0 S w=(test0 S w)^2 := by
  have hr87 : r87 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=87) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg126 : w 126=((1 : ℚ)*(w 37)*(w 37)) := by dsimp only [r87] at hr87; linear_combination hr87
  dsimp only [leaf0,test0]
  rw [hg126]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf1 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 58)) ((2 : ℚ)*(w 59)))
@[expose] def test1 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 1)) ((1 : ℚ)*(w 2)))
theorem leaf1_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf1 S w=(test1 S w)^2 := by
  have hr0 : r0 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=0) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg58 : w 58=((1 : ℚ)*(w 1)*(w 1) + (2 : ℚ)*(w 2)*(w 2)) := by dsimp only [r0] at hr0; linear_combination hr0
  have hr1 : r1 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=1) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg59 : w 59=((1 : ℚ)*(w 1)*(w 2)) := by dsimp only [r1] at hr1; linear_combination hr1
  dsimp only [leaf1,test1]
  rw [hg58,hg59]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf2 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 60)) ((2 : ℚ)*(w 61)))
@[expose] def test2 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 5)) ((1 : ℚ)*(w 6)))
theorem leaf2_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf2 S w=(test2 S w)^2 := by
  have hr4 : r4 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=4) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg60 : w 60=((1 : ℚ)*(w 5)*(w 5) + (2 : ℚ)*(w 6)*(w 6)) := by dsimp only [r4] at hr4; linear_combination hr4
  have hr5 : r5 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=5) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg61 : w 61=((1 : ℚ)*(w 5)*(w 6)) := by dsimp only [r5] at hr5; linear_combination hr5
  dsimp only [leaf2,test2]
  rw [hg60,hg61]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf3 (S : ℚ) (w : Assignment) : K := (pair ((2 : ℚ)*(w 62)) ((2 : ℚ)*(w 63)))
@[expose] def test3 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 9)) ((1 : ℚ)*(w 10)))
theorem leaf3_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf3 S w=(test3 S w)^2 := by
  have hr8 : r8 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=8) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg62 : w 62=((1 : ℚ)*(w 10)*(w 10) + (1 / 2 : ℚ)*(w 9)*(w 9)) := by dsimp only [r8] at hr8; linear_combination hr8
  have hr9 : r9 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=9) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg63 : w 63=((1 : ℚ)*(w 9)*(w 10)) := by dsimp only [r9] at hr9; linear_combination hr9
  dsimp only [leaf3,test3]
  rw [hg62,hg63]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf4 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 64)) ((2 : ℚ)*(w 65)))
@[expose] def test4 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 13)) ((1 : ℚ)*(w 14)))
theorem leaf4_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf4 S w=(test4 S w)^2 := by
  have hr12 : r12 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=12) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg64 : w 64=((1 : ℚ)*(w 13)*(w 13) + (2 : ℚ)*(w 14)*(w 14)) := by dsimp only [r12] at hr12; linear_combination hr12
  have hr13 : r13 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=13) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg65 : w 65=((1 : ℚ)*(w 13)*(w 14)) := by dsimp only [r13] at hr13; linear_combination hr13
  dsimp only [leaf4,test4]
  rw [hg64,hg65]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf5 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 125)) (0 : ℚ))
@[expose] def test5 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 76)*(w 76) + (-2 : ℚ)*(w 77)*(w 77)) (0 : ℚ))
theorem leaf5_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf5 S w=(test5 S w)^2 := by
  have hr86 : r86 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=86) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg125 : w 125=((1 : ℚ)*(w 90)*(w 90) + (-8 : ℚ)*(w 91)*(w 91)) := by dsimp only [r86] at hr86; linear_combination hr86
  have hr51 : r51 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=51) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg90 : w 90=((1 : ℚ)*(w 76)*(w 76) + (2 : ℚ)*(w 77)*(w 77)) := by dsimp only [r51] at hr51; linear_combination hr51
  have hr52 : r52 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=52) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg91 : w 91=((1 : ℚ)*(w 76)*(w 77)) := by dsimp only [r52] at hr52; linear_combination hr52
  dsimp only [leaf5,test5]
  rw [hg125,hg90,hg91]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf6 (S : ℚ) (w : Assignment) : K := (pair ((-1 : ℚ) + (1 : ℚ)*(w 19)) ((-1 : ℚ)*(w 20)))
@[expose] def leaf7 (S : ℚ) (w : Assignment) : K := (pair ((-1 : ℚ) + (1 : ℚ)*(w 23)) ((-1 : ℚ)*(w 24)))
@[expose] def leaf8 (S : ℚ) (w : Assignment) : K := (pair ((-1 : ℚ) + (1 : ℚ)*(w 27)) ((-1 : ℚ)*(w 28)))
@[expose] def leaf9 (S : ℚ) (w : Assignment) : K := (pair ((-1 : ℚ) + (1 : ℚ)*(w 31)) ((-1 : ℚ)*(w 32)))
@[expose] def leaf10 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 127)) ((2 : ℚ)*(w 128)))
@[expose] def test10 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 102) + (-1 : ℚ)*(w 104)) ((1 : ℚ)*(w 103) + (1 : ℚ)*(w 105)))
theorem leaf10_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf10 S w=(test10 S w)^2 := by
  have hr88 : r88 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=88) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg127 : w 127=((1 : ℚ)*(w 102)*(w 102) + (-2 : ℚ)*(w 102)*(w 104) + (2 : ℚ)*(w 103)*(w 103) + (4 : ℚ)*(w 103)*(w 105) + (1 : ℚ)*(w 104)*(w 104) + (2 : ℚ)*(w 105)*(w 105)) := by dsimp only [r88] at hr88; linear_combination hr88
  have hr89 : r89 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=89) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg128 : w 128=((1 : ℚ)*(w 102)*(w 103) + (1 : ℚ)*(w 102)*(w 105) + (-1 : ℚ)*(w 103)*(w 104) + (-1 : ℚ)*(w 104)*(w 105)) := by dsimp only [r89] at hr89; linear_combination hr89
  dsimp only [leaf10,test10]
  rw [hg127,hg128]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf11 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 129)) ((2 : ℚ)*(w 130)))
@[expose] def test11 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 106) + (-1 : ℚ)*(w 108)) ((1 : ℚ)*(w 107) + (1 : ℚ)*(w 109)))
theorem leaf11_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf11 S w=(test11 S w)^2 := by
  have hr90 : r90 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=90) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg129 : w 129=((1 : ℚ)*(w 106)*(w 106) + (-2 : ℚ)*(w 106)*(w 108) + (2 : ℚ)*(w 107)*(w 107) + (4 : ℚ)*(w 107)*(w 109) + (1 : ℚ)*(w 108)*(w 108) + (2 : ℚ)*(w 109)*(w 109)) := by dsimp only [r90] at hr90; linear_combination hr90
  have hr91 : r91 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=91) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg130 : w 130=((1 : ℚ)*(w 106)*(w 107) + (1 : ℚ)*(w 106)*(w 109) + (-1 : ℚ)*(w 107)*(w 108) + (-1 : ℚ)*(w 108)*(w 109)) := by dsimp only [r91] at hr91; linear_combination hr91
  dsimp only [leaf11,test11]
  rw [hg129,hg130]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf12 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 131)) ((2 : ℚ)*(w 132)))
@[expose] def test12 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 110) + (-1 : ℚ)*(w 112)) ((1 : ℚ)*(w 111) + (1 : ℚ)*(w 113)))
theorem leaf12_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf12 S w=(test12 S w)^2 := by
  have hr92 : r92 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=92) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg131 : w 131=((1 : ℚ)*(w 110)*(w 110) + (-2 : ℚ)*(w 110)*(w 112) + (2 : ℚ)*(w 111)*(w 111) + (4 : ℚ)*(w 111)*(w 113) + (1 : ℚ)*(w 112)*(w 112) + (2 : ℚ)*(w 113)*(w 113)) := by dsimp only [r92] at hr92; linear_combination hr92
  have hr93 : r93 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=93) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg132 : w 132=((1 : ℚ)*(w 110)*(w 111) + (1 : ℚ)*(w 110)*(w 113) + (-1 : ℚ)*(w 111)*(w 112) + (-1 : ℚ)*(w 112)*(w 113)) := by dsimp only [r93] at hr93; linear_combination hr93
  dsimp only [leaf12,test12]
  rw [hg131,hg132]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf13 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 133)) ((2 : ℚ)*(w 134)))
@[expose] def test13 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 114) + (-1 : ℚ)*(w 116)) ((1 : ℚ)*(w 115) + (1 : ℚ)*(w 117)))
theorem leaf13_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf13 S w=(test13 S w)^2 := by
  have hr94 : r94 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=94) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg133 : w 133=((1 : ℚ)*(w 114)*(w 114) + (-2 : ℚ)*(w 114)*(w 116) + (2 : ℚ)*(w 115)*(w 115) + (4 : ℚ)*(w 115)*(w 117) + (1 : ℚ)*(w 116)*(w 116) + (2 : ℚ)*(w 117)*(w 117)) := by dsimp only [r94] at hr94; linear_combination hr94
  have hr95 : r95 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=95) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg134 : w 134=((1 : ℚ)*(w 114)*(w 115) + (1 : ℚ)*(w 114)*(w 117) + (-1 : ℚ)*(w 115)*(w 116) + (-1 : ℚ)*(w 116)*(w 117)) := by dsimp only [r95] at hr95; linear_combination hr95
  dsimp only [leaf13,test13]
  rw [hg133,hg134]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf14 (S : ℚ) (w : Assignment) : K := (pair ((13860729 : ℚ) + (110885832 : ℚ)*(w 0) + (-7446 : ℚ)*(w 102) + (110885832 : ℚ)*(w 118) + (221771664 : ℚ)*(w 135)) ((-7446 : ℚ)*(w 103) + (-29784 : ℚ)*(w 136)))
@[expose] def test14 (S : ℚ) (w : Assignment) : K := (pair ((-3723 : ℚ) + (-14892 : ℚ)*(w 0) + (1 : ℚ)*(w 102) + (-14892 : ℚ)*(w 118)) ((1 : ℚ)*(w 103)))
theorem leaf14_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf14 S w=(test14 S w)^2 := by
  have hr96 : r96 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=96) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg135 : w 135=((1 : ℚ)*(w 0)*(w 0) + (-1 / 7446 : ℚ)*(w 0)*(w 102) + (2 : ℚ)*(w 0)*(w 118) + (1 / 221771664 : ℚ)*(w 102)*(w 102) + (-1 / 7446 : ℚ)*(w 102)*(w 118) + (1 / 110885832 : ℚ)*(w 103)*(w 103) + (1 : ℚ)*(w 118)*(w 118)) := by dsimp only [r96] at hr96; linear_combination hr96
  have hr97 : r97 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=97) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg136 : w 136=((1 : ℚ)*(w 0)*(w 103) + (-1 / 14892 : ℚ)*(w 102)*(w 103) + (1 : ℚ)*(w 103)*(w 118)) := by dsimp only [r97] at hr97; linear_combination hr97
  dsimp only [leaf14,test14]
  rw [hg135,hg136]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def leaf15 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ) + (-2 : ℚ)*(w 123) + (1 : ℚ)*(w 137)) ((-4 : ℚ)*(w 124) + (4 : ℚ)*(w 138)))
@[expose] def test15 (S : ℚ) (w : Assignment) : K := (pair ((-1 : ℚ) + (1 : ℚ)*(w 123)) ((2 : ℚ)*(w 124)))
theorem leaf15_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf15 S w=(test15 S w)^2 := by
  have hr98 : r98 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=98) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg137 : w 137=((1 : ℚ)*(w 123)*(w 123) + (8 : ℚ)*(w 124)*(w 124)) := by dsimp only [r98] at hr98; linear_combination hr98
  have hr99 : r99 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=99) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg138 : w 138=((1 : ℚ)*(w 123)*(w 124)) := by dsimp only [r99] at hr99; linear_combination hr99
  dsimp only [leaf15,test15]
  rw [hg137,hg138]
  ext <;> norm_num [pair,pow_two] <;> ring

@[expose] def q0_1 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 151)) 0
@[expose] def q0_4 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 156)) 0
@[expose] def q0_13 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 158)) 0
@[expose] def node0_0 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 159)) (0 : ℚ))
theorem step0_0 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_0 S w=(pair 1 0)^2+q0_4 S w*leaf0 S w := by
  have hr120 : r120 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=120) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_0,q0_4,leaf0,pair,pow_two]
  · dsimp only [r120] at hr120; linear_combination hr120

@[expose] def node0_1 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 160)) (0 : ℚ))
theorem step0_1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_1 S w=(node0_0 S w)^2+q0_1 S w*leaf5 S w := by
  have hr121 : r121 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=121) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_1,q0_1,leaf5,node0_0,pair,pow_two]
  · dsimp only [r121] at hr121; linear_combination hr121

@[expose] def node0_2 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 161)) ((1 : ℚ)*(w 162)))
theorem step0_2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_2 S w=(node0_1 S w)^2+q0_1 S w*leaf1 S w := by
  have hr122 : r122 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=122) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr123 : r123 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=123) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_2,q0_1,leaf1,node0_1,pair,pow_two]
  · dsimp only [r122] at hr122; linear_combination hr122
  · dsimp only [r123] at hr123; linear_combination hr123

@[expose] def node0_3 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 163)) ((1 : ℚ)*(w 164)))
theorem step0_3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_3 S w=(node0_2 S w)^2+q0_1 S w*leaf2 S w := by
  have hr124 : r124 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=124) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr125 : r125 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=125) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_3,q0_1,leaf2,node0_2,pair,pow_two]
  · dsimp only [r124] at hr124; linear_combination hr124
  · dsimp only [r125] at hr125; linear_combination hr125

@[expose] def node0_4 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 165)) ((1 : ℚ)*(w 166)))
theorem step0_4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_4 S w=(node0_3 S w)^2+q0_1 S w*leaf3 S w := by
  have hr126 : r126 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=126) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr127 : r127 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=127) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_4,q0_1,leaf3,node0_3,pair,pow_two]
  · dsimp only [r126] at hr126; linear_combination hr126
  · dsimp only [r127] at hr127; linear_combination hr127

@[expose] def node0_5 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 167)) ((1 : ℚ)*(w 168)))
theorem step0_5 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_5 S w=(node0_4 S w)^2+q0_1 S w*leaf4 S w := by
  have hr128 : r128 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=128) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr129 : r129 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=129) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_5,q0_1,leaf4,node0_4,pair,pow_two]
  · dsimp only [r128] at hr128; linear_combination hr128
  · dsimp only [r129] at hr129; linear_combination hr129

@[expose] def node0_6 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 169)) ((1 : ℚ)*(w 170)))
theorem step0_6 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_6 S w=(node0_5 S w)^2+q0_1 S w*leaf6 S w := by
  have hr130 : r130 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=130) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr131 : r131 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=131) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_6,q0_1,leaf6,node0_5,pair,pow_two]
  · dsimp only [r130] at hr130; linear_combination hr130
  · dsimp only [r131] at hr131; linear_combination hr131

@[expose] def node0_7 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 171)) ((1 : ℚ)*(w 172)))
theorem step0_7 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_7 S w=(node0_6 S w)^2+q0_1 S w*leaf7 S w := by
  have hr132 : r132 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=132) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr133 : r133 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=133) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_7,q0_1,leaf7,node0_6,pair,pow_two]
  · dsimp only [r132] at hr132; linear_combination hr132
  · dsimp only [r133] at hr133; linear_combination hr133

@[expose] def node0_8 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 173)) ((1 : ℚ)*(w 174)))
theorem step0_8 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_8 S w=(node0_7 S w)^2+q0_1 S w*leaf8 S w := by
  have hr134 : r134 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=134) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr135 : r135 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=135) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_8,q0_1,leaf8,node0_7,pair,pow_two]
  · dsimp only [r134] at hr134; linear_combination hr134
  · dsimp only [r135] at hr135; linear_combination hr135

@[expose] def node0_9 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 175)) ((1 : ℚ)*(w 176)))
theorem step0_9 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_9 S w=(node0_8 S w)^2+q0_1 S w*leaf9 S w := by
  have hr136 : r136 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=136) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr137 : r137 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=137) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_9,q0_1,leaf9,node0_8,pair,pow_two]
  · dsimp only [r136] at hr136; linear_combination hr136
  · dsimp only [r137] at hr137; linear_combination hr137

@[expose] def node0_10 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 177)) ((1 : ℚ)*(w 178)))
theorem step0_10 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_10 S w=(node0_9 S w)^2+q0_4 S w*leaf10 S w := by
  have hr138 : r138 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=138) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr139 : r139 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=139) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_10,q0_4,leaf10,node0_9,pair,pow_two]
  · dsimp only [r138] at hr138; linear_combination hr138
  · dsimp only [r139] at hr139; linear_combination hr139

@[expose] def node0_11 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 179)) ((1 : ℚ)*(w 180)))
theorem step0_11 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_11 S w=(node0_10 S w)^2+q0_13 S w*leaf11 S w := by
  have hr140 : r140 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=140) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr141 : r141 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=141) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_11,q0_13,leaf11,node0_10,pair,pow_two]
  · dsimp only [r140] at hr140; linear_combination hr140
  · dsimp only [r141] at hr141; linear_combination hr141

@[expose] def node0_12 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 181)) ((1 : ℚ)*(w 182)))
theorem step0_12 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_12 S w=(node0_11 S w)^2+q0_13 S w*leaf12 S w := by
  have hr142 : r142 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=142) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr143 : r143 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=143) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_12,q0_13,leaf12,node0_11,pair,pow_two]
  · dsimp only [r142] at hr142; linear_combination hr142
  · dsimp only [r143] at hr143; linear_combination hr143

@[expose] def node0_13 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 183)) ((1 : ℚ)*(w 184)))
theorem step0_13 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_13 S w=(node0_12 S w)^2+q0_13 S w*leaf13 S w := by
  have hr144 : r144 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=144) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr145 : r145 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=145) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_13,q0_13,leaf13,node0_12,pair,pow_two]
  · dsimp only [r144] at hr144; linear_combination hr144
  · dsimp only [r145] at hr145; linear_combination hr145

@[expose] def node0_14 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 185)) ((1 : ℚ)*(w 186)))
theorem step0_14 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_14 S w=(node0_13 S w)^2+q0_4 S w*leaf14 S w := by
  have hr146 : r146 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=146) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr147 : r147 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=147) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_14,q0_4,leaf14,node0_13,pair,pow_two]
  · dsimp only [r146] at hr146; linear_combination hr146
  · dsimp only [r147] at hr147; linear_combination hr147

@[expose] def node0_15 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 187)) ((1 : ℚ)*(w 188)))
theorem step0_15 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node0_15 S w=(node0_14 S w)^2+q0_13 S w*leaf15 S w := by
  have hr148 : r148 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=148) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr149 : r149 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=149) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node0_15,q0_13,leaf15,node0_14,pair,pow_two]
  · dsimp only [r148] at hr148; linear_combination hr148
  · dsimp only [r149] at hr149; linear_combination hr149

@[expose] def detector0_leaves (S : ℚ) (w : Assignment) : List (K×K) := [(q0_4 S w,leaf0 S w), (q0_1 S w,leaf5 S w), (q0_1 S w,leaf1 S w), (q0_1 S w,leaf2 S w), (q0_1 S w,leaf3 S w), (q0_1 S w,leaf4 S w), (q0_1 S w,leaf6 S w), (q0_1 S w,leaf7 S w), (q0_1 S w,leaf8 S w), (q0_1 S w,leaf9 S w), (q0_4 S w,leaf10 S w), (q0_13 S w,leaf11 S w), (q0_13 S w,leaf12 S w), (q0_13 S w,leaf13 S w), (q0_4 S w,leaf14 S w), (q0_13 S w,leaf15 S w)]
theorem detector0_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (detector0_leaves S w).foldl (fun previous p => previous^2+p.1*p.2) 1=node0_15 S w := by
  simp only [detector0_leaves,List.foldl_cons,List.foldl_nil]
  have hone : (1:K)=pair 1 0 := rfl
  rw [hone]
  rw [←step0_0 S w source,←step0_1 S w source,←step0_2 S w source,←step0_3 S w source,←step0_4 S w source,←step0_5 S w source,←step0_6 S w source,←step0_7 S w source,←step0_8 S w source,←step0_9 S w source,←step0_10 S w source,←step0_11 S w source,←step0_12 S w source,←step0_13 S w source,←step0_14 S w source,←step0_15 S w source]

theorem detector0_terminal (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    2*((1 : ℚ)*(w 187))*((1 : ℚ)*(w 189))=((1 : ℚ)*(w 187))^2-2*((1 : ℚ)*(w 188))^2 ∧ ((1 : ℚ)*(w 190))*((1 : ℚ)*(w 151) + (1 : ℚ)*(w 152) + (-1 : ℚ)*(w 153))=((1 : ℚ)*(w 189))^2 := by
  have hr150 : r150 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=150) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr151 : r151 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=151) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  constructor
  · dsimp only [r150] at hr150; linear_combination 2*hr150
  · dsimp only [r151] at hr151; linear_combination hr151

@[expose] def q1_1 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 203)) 0
@[expose] def q1_4 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 207)) 0
@[expose] def q1_13 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 209)) 0
@[expose] def node1_0 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 210)) (0 : ℚ))
theorem step1_0 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_0 S w=(pair 1 0)^2+q1_4 S w*leaf0 S w := by
  have hr173 : r173 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=173) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_0,q1_4,leaf0,pair,pow_two]
  · dsimp only [r173] at hr173; linear_combination hr173

@[expose] def node1_1 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 211)) (0 : ℚ))
theorem step1_1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_1 S w=(node1_0 S w)^2+q1_1 S w*leaf5 S w := by
  have hr174 : r174 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=174) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_1,q1_1,leaf5,node1_0,pair,pow_two]
  · dsimp only [r174] at hr174; linear_combination hr174

@[expose] def node1_2 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 212)) ((1 : ℚ)*(w 213)))
theorem step1_2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_2 S w=(node1_1 S w)^2+q1_1 S w*leaf1 S w := by
  have hr175 : r175 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=175) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr176 : r176 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=176) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_2,q1_1,leaf1,node1_1,pair,pow_two]
  · dsimp only [r175] at hr175; linear_combination hr175
  · dsimp only [r176] at hr176; linear_combination hr176

@[expose] def node1_3 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 214)) ((1 : ℚ)*(w 215)))
theorem step1_3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_3 S w=(node1_2 S w)^2+q1_1 S w*leaf2 S w := by
  have hr177 : r177 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=177) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr178 : r178 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=178) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_3,q1_1,leaf2,node1_2,pair,pow_two]
  · dsimp only [r177] at hr177; linear_combination hr177
  · dsimp only [r178] at hr178; linear_combination hr178

@[expose] def node1_4 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 216)) ((1 : ℚ)*(w 217)))
theorem step1_4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_4 S w=(node1_3 S w)^2+q1_1 S w*leaf3 S w := by
  have hr179 : r179 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=179) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr180 : r180 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=180) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_4,q1_1,leaf3,node1_3,pair,pow_two]
  · dsimp only [r179] at hr179; linear_combination hr179
  · dsimp only [r180] at hr180; linear_combination hr180

@[expose] def node1_5 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 218)) ((1 : ℚ)*(w 219)))
theorem step1_5 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_5 S w=(node1_4 S w)^2+q1_1 S w*leaf4 S w := by
  have hr181 : r181 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=181) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr182 : r182 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=182) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_5,q1_1,leaf4,node1_4,pair,pow_two]
  · dsimp only [r181] at hr181; linear_combination hr181
  · dsimp only [r182] at hr182; linear_combination hr182

@[expose] def node1_6 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 220)) ((1 : ℚ)*(w 221)))
theorem step1_6 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_6 S w=(node1_5 S w)^2+q1_1 S w*leaf6 S w := by
  have hr183 : r183 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=183) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr184 : r184 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=184) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_6,q1_1,leaf6,node1_5,pair,pow_two]
  · dsimp only [r183] at hr183; linear_combination hr183
  · dsimp only [r184] at hr184; linear_combination hr184

@[expose] def node1_7 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 222)) ((1 : ℚ)*(w 223)))
theorem step1_7 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_7 S w=(node1_6 S w)^2+q1_1 S w*leaf7 S w := by
  have hr185 : r185 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=185) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr186 : r186 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=186) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_7,q1_1,leaf7,node1_6,pair,pow_two]
  · dsimp only [r185] at hr185; linear_combination hr185
  · dsimp only [r186] at hr186; linear_combination hr186

@[expose] def node1_8 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 224)) ((1 : ℚ)*(w 225)))
theorem step1_8 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_8 S w=(node1_7 S w)^2+q1_1 S w*leaf8 S w := by
  have hr187 : r187 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=187) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr188 : r188 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=188) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_8,q1_1,leaf8,node1_7,pair,pow_two]
  · dsimp only [r187] at hr187; linear_combination hr187
  · dsimp only [r188] at hr188; linear_combination hr188

@[expose] def node1_9 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 226)) ((1 : ℚ)*(w 227)))
theorem step1_9 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_9 S w=(node1_8 S w)^2+q1_1 S w*leaf9 S w := by
  have hr189 : r189 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=189) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr190 : r190 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=190) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_9,q1_1,leaf9,node1_8,pair,pow_two]
  · dsimp only [r189] at hr189; linear_combination hr189
  · dsimp only [r190] at hr190; linear_combination hr190

@[expose] def node1_10 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 228)) ((1 : ℚ)*(w 229)))
theorem step1_10 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_10 S w=(node1_9 S w)^2+q1_4 S w*leaf10 S w := by
  have hr191 : r191 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=191) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr192 : r192 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=192) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_10,q1_4,leaf10,node1_9,pair,pow_two]
  · dsimp only [r191] at hr191; linear_combination hr191
  · dsimp only [r192] at hr192; linear_combination hr192

@[expose] def node1_11 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 230)) ((1 : ℚ)*(w 231)))
theorem step1_11 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_11 S w=(node1_10 S w)^2+q1_13 S w*leaf11 S w := by
  have hr193 : r193 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=193) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr194 : r194 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=194) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_11,q1_13,leaf11,node1_10,pair,pow_two]
  · dsimp only [r193] at hr193; linear_combination hr193
  · dsimp only [r194] at hr194; linear_combination hr194

@[expose] def node1_12 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 232)) ((1 : ℚ)*(w 233)))
theorem step1_12 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_12 S w=(node1_11 S w)^2+q1_13 S w*leaf12 S w := by
  have hr195 : r195 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=195) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr196 : r196 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=196) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_12,q1_13,leaf12,node1_11,pair,pow_two]
  · dsimp only [r195] at hr195; linear_combination hr195
  · dsimp only [r196] at hr196; linear_combination hr196

@[expose] def node1_13 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 234)) ((1 : ℚ)*(w 235)))
theorem step1_13 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_13 S w=(node1_12 S w)^2+q1_13 S w*leaf13 S w := by
  have hr197 : r197 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=197) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr198 : r198 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=198) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_13,q1_13,leaf13,node1_12,pair,pow_two]
  · dsimp only [r197] at hr197; linear_combination hr197
  · dsimp only [r198] at hr198; linear_combination hr198

@[expose] def node1_14 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 236)) ((1 : ℚ)*(w 237)))
theorem step1_14 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_14 S w=(node1_13 S w)^2+q1_4 S w*leaf14 S w := by
  have hr199 : r199 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=199) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr200 : r200 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=200) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_14,q1_4,leaf14,node1_13,pair,pow_two]
  · dsimp only [r199] at hr199; linear_combination hr199
  · dsimp only [r200] at hr200; linear_combination hr200

@[expose] def node1_15 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 238)) ((1 : ℚ)*(w 239)))
theorem step1_15 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node1_15 S w=(node1_14 S w)^2+q1_13 S w*leaf15 S w := by
  have hr201 : r201 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=201) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr202 : r202 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=202) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node1_15,q1_13,leaf15,node1_14,pair,pow_two]
  · dsimp only [r201] at hr201; linear_combination hr201
  · dsimp only [r202] at hr202; linear_combination hr202

@[expose] def detector1_leaves (S : ℚ) (w : Assignment) : List (K×K) := [(q1_4 S w,leaf0 S w), (q1_1 S w,leaf5 S w), (q1_1 S w,leaf1 S w), (q1_1 S w,leaf2 S w), (q1_1 S w,leaf3 S w), (q1_1 S w,leaf4 S w), (q1_1 S w,leaf6 S w), (q1_1 S w,leaf7 S w), (q1_1 S w,leaf8 S w), (q1_1 S w,leaf9 S w), (q1_4 S w,leaf10 S w), (q1_13 S w,leaf11 S w), (q1_13 S w,leaf12 S w), (q1_13 S w,leaf13 S w), (q1_4 S w,leaf14 S w), (q1_13 S w,leaf15 S w)]
theorem detector1_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (detector1_leaves S w).foldl (fun previous p => previous^2+p.1*p.2) 1=node1_15 S w := by
  simp only [detector1_leaves,List.foldl_cons,List.foldl_nil]
  have hone : (1:K)=pair 1 0 := rfl
  rw [hone]
  rw [←step1_0 S w source,←step1_1 S w source,←step1_2 S w source,←step1_3 S w source,←step1_4 S w source,←step1_5 S w source,←step1_6 S w source,←step1_7 S w source,←step1_8 S w source,←step1_9 S w source,←step1_10 S w source,←step1_11 S w source,←step1_12 S w source,←step1_13 S w source,←step1_14 S w source,←step1_15 S w source]

theorem detector1_terminal (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    2*((1 : ℚ)*(w 238))*((1 : ℚ)*(w 240))=((1 : ℚ)*(w 238))^2-2*((1 : ℚ)*(w 239))^2 ∧ ((1 : ℚ)*(w 241))*((-1 : ℚ)*(w 201) + (1 : ℚ)*(w 204))=((1 : ℚ)*(w 240))^2 := by
  have hr203 : r203 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=203) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr204 : r204 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=204) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  constructor
  · dsimp only [r203] at hr203; linear_combination 2*hr203
  · dsimp only [r204] at hr204; linear_combination hr204

@[expose] def q2_1 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 254)) 0
@[expose] def q2_4 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 258)) 0
@[expose] def q2_13 (S : ℚ) (w : Assignment) : K := pair ((1 : ℚ)*(w 260)) 0
@[expose] def node2_0 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 261)) (0 : ℚ))
theorem step2_0 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_0 S w=(pair 1 0)^2+q2_4 S w*leaf0 S w := by
  have hr226 : r226 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=226) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_0,q2_4,leaf0,pair,pow_two]
  · dsimp only [r226] at hr226; linear_combination hr226

@[expose] def node2_1 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 262)) (0 : ℚ))
theorem step2_1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_1 S w=(node2_0 S w)^2+q2_1 S w*leaf5 S w := by
  have hr227 : r227 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=227) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_1,q2_1,leaf5,node2_0,pair,pow_two]
  · dsimp only [r227] at hr227; linear_combination hr227

@[expose] def node2_2 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 263)) ((1 : ℚ)*(w 264)))
theorem step2_2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_2 S w=(node2_1 S w)^2+q2_1 S w*leaf1 S w := by
  have hr228 : r228 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=228) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr229 : r229 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=229) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_2,q2_1,leaf1,node2_1,pair,pow_two]
  · dsimp only [r228] at hr228; linear_combination hr228
  · dsimp only [r229] at hr229; linear_combination hr229

@[expose] def node2_3 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 265)) ((1 : ℚ)*(w 266)))
theorem step2_3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_3 S w=(node2_2 S w)^2+q2_1 S w*leaf2 S w := by
  have hr230 : r230 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=230) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr231 : r231 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=231) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_3,q2_1,leaf2,node2_2,pair,pow_two]
  · dsimp only [r230] at hr230; linear_combination hr230
  · dsimp only [r231] at hr231; linear_combination hr231

@[expose] def node2_4 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 267)) ((1 : ℚ)*(w 268)))
theorem step2_4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_4 S w=(node2_3 S w)^2+q2_1 S w*leaf3 S w := by
  have hr232 : r232 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=232) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr233 : r233 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=233) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_4,q2_1,leaf3,node2_3,pair,pow_two]
  · dsimp only [r232] at hr232; linear_combination hr232
  · dsimp only [r233] at hr233; linear_combination hr233

@[expose] def node2_5 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 269)) ((1 : ℚ)*(w 270)))
theorem step2_5 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_5 S w=(node2_4 S w)^2+q2_1 S w*leaf4 S w := by
  have hr234 : r234 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=234) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr235 : r235 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=235) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_5,q2_1,leaf4,node2_4,pair,pow_two]
  · dsimp only [r234] at hr234; linear_combination hr234
  · dsimp only [r235] at hr235; linear_combination hr235

@[expose] def node2_6 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 271)) ((1 : ℚ)*(w 272)))
theorem step2_6 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_6 S w=(node2_5 S w)^2+q2_1 S w*leaf6 S w := by
  have hr236 : r236 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=236) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr237 : r237 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=237) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_6,q2_1,leaf6,node2_5,pair,pow_two]
  · dsimp only [r236] at hr236; linear_combination hr236
  · dsimp only [r237] at hr237; linear_combination hr237

@[expose] def node2_7 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 273)) ((1 : ℚ)*(w 274)))
theorem step2_7 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_7 S w=(node2_6 S w)^2+q2_1 S w*leaf7 S w := by
  have hr238 : r238 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=238) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr239 : r239 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=239) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_7,q2_1,leaf7,node2_6,pair,pow_two]
  · dsimp only [r238] at hr238; linear_combination hr238
  · dsimp only [r239] at hr239; linear_combination hr239

@[expose] def node2_8 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 275)) ((1 : ℚ)*(w 276)))
theorem step2_8 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_8 S w=(node2_7 S w)^2+q2_1 S w*leaf8 S w := by
  have hr240 : r240 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=240) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr241 : r241 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=241) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_8,q2_1,leaf8,node2_7,pair,pow_two]
  · dsimp only [r240] at hr240; linear_combination hr240
  · dsimp only [r241] at hr241; linear_combination hr241

@[expose] def node2_9 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 277)) ((1 : ℚ)*(w 278)))
theorem step2_9 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_9 S w=(node2_8 S w)^2+q2_1 S w*leaf9 S w := by
  have hr242 : r242 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=242) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr243 : r243 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=243) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_9,q2_1,leaf9,node2_8,pair,pow_two]
  · dsimp only [r242] at hr242; linear_combination hr242
  · dsimp only [r243] at hr243; linear_combination hr243

@[expose] def node2_10 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 279)) ((1 : ℚ)*(w 280)))
theorem step2_10 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_10 S w=(node2_9 S w)^2+q2_4 S w*leaf10 S w := by
  have hr244 : r244 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=244) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr245 : r245 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=245) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_10,q2_4,leaf10,node2_9,pair,pow_two]
  · dsimp only [r244] at hr244; linear_combination hr244
  · dsimp only [r245] at hr245; linear_combination hr245

@[expose] def node2_11 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 281)) ((1 : ℚ)*(w 282)))
theorem step2_11 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_11 S w=(node2_10 S w)^2+q2_13 S w*leaf11 S w := by
  have hr246 : r246 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=246) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr247 : r247 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=247) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_11,q2_13,leaf11,node2_10,pair,pow_two]
  · dsimp only [r246] at hr246; linear_combination hr246
  · dsimp only [r247] at hr247; linear_combination hr247

@[expose] def node2_12 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 283)) ((1 : ℚ)*(w 284)))
theorem step2_12 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_12 S w=(node2_11 S w)^2+q2_13 S w*leaf12 S w := by
  have hr248 : r248 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=248) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr249 : r249 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=249) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_12,q2_13,leaf12,node2_11,pair,pow_two]
  · dsimp only [r248] at hr248; linear_combination hr248
  · dsimp only [r249] at hr249; linear_combination hr249

@[expose] def node2_13 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 285)) ((1 : ℚ)*(w 286)))
theorem step2_13 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_13 S w=(node2_12 S w)^2+q2_13 S w*leaf13 S w := by
  have hr250 : r250 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=250) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr251 : r251 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=251) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_13,q2_13,leaf13,node2_12,pair,pow_two]
  · dsimp only [r250] at hr250; linear_combination hr250
  · dsimp only [r251] at hr251; linear_combination hr251

@[expose] def node2_14 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 287)) ((1 : ℚ)*(w 288)))
theorem step2_14 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_14 S w=(node2_13 S w)^2+q2_4 S w*leaf14 S w := by
  have hr252 : r252 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=252) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr253 : r253 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=253) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_14,q2_4,leaf14,node2_13,pair,pow_two]
  · dsimp only [r252] at hr252; linear_combination hr252
  · dsimp only [r253] at hr253; linear_combination hr253

@[expose] def node2_15 (S : ℚ) (w : Assignment) : K := (pair ((1 : ℚ)*(w 289)) ((1 : ℚ)*(w 290)))
theorem step2_15 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    node2_15 S w=(node2_14 S w)^2+q2_13 S w*leaf15 S w := by
  have hr254 : r254 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=254) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr255 : r255 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=255) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [node2_15,q2_13,leaf15,node2_14,pair,pow_two]
  · dsimp only [r254] at hr254; linear_combination hr254
  · dsimp only [r255] at hr255; linear_combination hr255

@[expose] def detector2_leaves (S : ℚ) (w : Assignment) : List (K×K) := [(q2_4 S w,leaf0 S w), (q2_1 S w,leaf5 S w), (q2_1 S w,leaf1 S w), (q2_1 S w,leaf2 S w), (q2_1 S w,leaf3 S w), (q2_1 S w,leaf4 S w), (q2_1 S w,leaf6 S w), (q2_1 S w,leaf7 S w), (q2_1 S w,leaf8 S w), (q2_1 S w,leaf9 S w), (q2_4 S w,leaf10 S w), (q2_13 S w,leaf11 S w), (q2_13 S w,leaf12 S w), (q2_13 S w,leaf13 S w), (q2_4 S w,leaf14 S w), (q2_13 S w,leaf15 S w)]
theorem detector2_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (detector2_leaves S w).foldl (fun previous p => previous^2+p.1*p.2) 1=node2_15 S w := by
  simp only [detector2_leaves,List.foldl_cons,List.foldl_nil]
  have hone : (1:K)=pair 1 0 := rfl
  rw [hone]
  rw [←step2_0 S w source,←step2_1 S w source,←step2_2 S w source,←step2_3 S w source,←step2_4 S w source,←step2_5 S w source,←step2_6 S w source,←step2_7 S w source,←step2_8 S w source,←step2_9 S w source,←step2_10 S w source,←step2_11 S w source,←step2_12 S w source,←step2_13 S w source,←step2_14 S w source,←step2_15 S w source]

theorem detector2_terminal (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    2*((1 : ℚ)*(w 289))*((1 : ℚ)*(w 291))=((1 : ℚ)*(w 289))^2-2*((1 : ℚ)*(w 290))^2 ∧ ((1 : ℚ)*(w 292))*((-1 : ℚ)*(w 252) + (1 : ℚ)*(w 255))=((1 : ℚ)*(w 291))^2 := by
  have hr256 : r256 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=256) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr257 : r257 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=257) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  constructor
  · dsimp only [r256] at hr256; linear_combination 2*hr256
  · dsimp only [r257] at hr257; linear_combination hr257

theorem leaf0_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf0 S w) := by
  rw [leaf0_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf1_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf1 S w) := by
  rw [leaf1_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf2_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf2 S w) := by
  rw [leaf2_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf3_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf3 S w) := by
  rw [leaf3_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf4_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf4 S w) := by
  rw [leaf4_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf5_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf5 S w) := by
  rw [leaf5_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf6_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf6 S w) := by
  simpa [leaf6,sub_eq_add_neg,add_comm] using RawReciprocal318.VA_linear_leaf_even S w source v hD h2

theorem leaf7_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf7 S w) := by
  simpa [leaf7,sub_eq_add_neg,add_comm] using RawReciprocal318.VS_linear_leaf_even S w source v hD h2

theorem leaf8_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf8 S w) := by
  simpa [leaf8,sub_eq_add_neg,add_comm] using RawReciprocal318.VT_linear_leaf_even S w source v hD h2

theorem leaf9_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf9 S w) := by
  simpa [leaf9,sub_eq_add_neg,add_comm] using RawReciprocal318.VZ_linear_leaf_even S w source v hD h2

theorem leaf10_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf10 S w) := by
  rw [leaf10_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf11_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf11 S w) := by
  rw [leaf11_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf12_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf12 S w) := by
  rw [leaf12_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf13_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf13 S w) := by
  rw [leaf13_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf14_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf14 S w) := by
  rw [leaf14_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem leaf15_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf15 S w) := by
  rw [leaf15_square S w source]
  exact ValuationEvenNormChain.square_even v _

theorem detector0_nonzero (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0)
    (hq1 : ValuationEvenNormChain.OddAt v (q0_1 S w))
    (hq4 : ValuationEvenNormChain.OddAt v (q0_4 S w))
    (hq13 : ValuationEvenNormChain.OddAt v (q0_13 S w)) : node0_15 S w≠0 := by
  rw [←detector0_actual S w source]
  apply ValuationEvenNormChain.fold_nonzero v _ _ ?_ one_ne_zero
  intro p hp
  simp only [detector0_leaves,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨hq4,leaf0_even S w source v hD h2⟩
  · exact ⟨hq1,leaf5_even S w source v hD h2⟩
  · exact ⟨hq1,leaf1_even S w source v hD h2⟩
  · exact ⟨hq1,leaf2_even S w source v hD h2⟩
  · exact ⟨hq1,leaf3_even S w source v hD h2⟩
  · exact ⟨hq1,leaf4_even S w source v hD h2⟩
  · exact ⟨hq1,leaf6_even S w source v hD h2⟩
  · exact ⟨hq1,leaf7_even S w source v hD h2⟩
  · exact ⟨hq1,leaf8_even S w source v hD h2⟩
  · exact ⟨hq1,leaf9_even S w source v hD h2⟩
  · exact ⟨hq4,leaf10_even S w source v hD h2⟩
  · exact ⟨hq13,leaf11_even S w source v hD h2⟩
  · exact ⟨hq13,leaf12_even S w source v hD h2⟩
  · exact ⟨hq13,leaf13_even S w source v hD h2⟩
  · exact ⟨hq4,leaf14_even S w source v hD h2⟩
  · exact ⟨hq13,leaf15_even S w source v hD h2⟩

theorem detector1_nonzero (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0)
    (hq1 : ValuationEvenNormChain.OddAt v (q1_1 S w))
    (hq4 : ValuationEvenNormChain.OddAt v (q1_4 S w))
    (hq13 : ValuationEvenNormChain.OddAt v (q1_13 S w)) : node1_15 S w≠0 := by
  rw [←detector1_actual S w source]
  apply ValuationEvenNormChain.fold_nonzero v _ _ ?_ one_ne_zero
  intro p hp
  simp only [detector1_leaves,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨hq4,leaf0_even S w source v hD h2⟩
  · exact ⟨hq1,leaf5_even S w source v hD h2⟩
  · exact ⟨hq1,leaf1_even S w source v hD h2⟩
  · exact ⟨hq1,leaf2_even S w source v hD h2⟩
  · exact ⟨hq1,leaf3_even S w source v hD h2⟩
  · exact ⟨hq1,leaf4_even S w source v hD h2⟩
  · exact ⟨hq1,leaf6_even S w source v hD h2⟩
  · exact ⟨hq1,leaf7_even S w source v hD h2⟩
  · exact ⟨hq1,leaf8_even S w source v hD h2⟩
  · exact ⟨hq1,leaf9_even S w source v hD h2⟩
  · exact ⟨hq4,leaf10_even S w source v hD h2⟩
  · exact ⟨hq13,leaf11_even S w source v hD h2⟩
  · exact ⟨hq13,leaf12_even S w source v hD h2⟩
  · exact ⟨hq13,leaf13_even S w source v hD h2⟩
  · exact ⟨hq4,leaf14_even S w source v hD h2⟩
  · exact ⟨hq13,leaf15_even S w source v hD h2⟩

theorem detector2_nonzero (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0)
    (hq1 : ValuationEvenNormChain.OddAt v (q2_1 S w))
    (hq4 : ValuationEvenNormChain.OddAt v (q2_4 S w))
    (hq13 : ValuationEvenNormChain.OddAt v (q2_13 S w)) : node2_15 S w≠0 := by
  rw [←detector2_actual S w source]
  apply ValuationEvenNormChain.fold_nonzero v _ _ ?_ one_ne_zero
  intro p hp
  simp only [detector2_leaves,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨hq4,leaf0_even S w source v hD h2⟩
  · exact ⟨hq1,leaf5_even S w source v hD h2⟩
  · exact ⟨hq1,leaf1_even S w source v hD h2⟩
  · exact ⟨hq1,leaf2_even S w source v hD h2⟩
  · exact ⟨hq1,leaf3_even S w source v hD h2⟩
  · exact ⟨hq1,leaf4_even S w source v hD h2⟩
  · exact ⟨hq1,leaf6_even S w source v hD h2⟩
  · exact ⟨hq1,leaf7_even S w source v hD h2⟩
  · exact ⟨hq1,leaf8_even S w source v hD h2⟩
  · exact ⟨hq1,leaf9_even S w source v hD h2⟩
  · exact ⟨hq4,leaf10_even S w source v hD h2⟩
  · exact ⟨hq13,leaf11_even S w source v hD h2⟩
  · exact ⟨hq13,leaf12_even S w source v hD h2⟩
  · exact ⟨hq13,leaf13_even S w source v hD h2⟩
  · exact ⟨hq4,leaf14_even S w source v hD h2⟩
  · exact ⟨hq13,leaf15_even S w source v hD h2⟩

end RawDetector318
