module
public import RootPointAlgebra318
public import RawAnchorNorm318
public section
namespace RawRootPoints318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root0_data (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (pair (w 3) (w 4))^2=1-D*(pair (w 1) (w 2))^4 ∧
    (pair (w 19) (w 20))^2=1-D*(pair (w 17) (w 18))^4 ∧
    (pair (w 17) (w 18))^2-(pair (w 1) (w 2))^2≠0 ∧
    ((pair (w 17) (w 18))^2-(pair (w 1) (w 2))^2)*RawAnchorNorm318.root w 0=
      pair (w 1) (w 2)*pair (w 19) (w 20)+pair (w 17) (w 18)*pair (w 3) (w 4) := by
  have h0 : r0 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=0)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r0] at h0
  have h1 : r1 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=1)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r1] at h1
  have h2 : r2 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=2)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r2] at h2
  have h3 : r3 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=3)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r3] at h3
  have h16 : r16 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=16)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r16] at h16
  have h17 : r17 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=17)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r17] at h17
  have h18 : r18 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=18)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r18] at h18
  have h19 : r19 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=19)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r19] at h19
  have h39 : r39 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=39)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r39] at h39
  have h40 : r40 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=40)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r40] at h40
  have h41 : r41 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=41)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r41] at h41
  have hfU : (pair (w 1) (w 2))^2=pair (1*w 58) (2*w 59) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -1*h0;linear_combination -2*h1]
  have hfV : (pair (w 17) (w 18))^2=pair (w 66) (2*w 67) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -h16;linear_combination -2*h17]
  have hu : (pair (w 3) (w 4))^2=1-D*(pair (w 1) (w 2))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfU]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h2;linear_combination h3]
  have hv : (pair (w 19) (w 20))^2=1-D*(pair (w 17) (w 18))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfV]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h18;linear_combination h19]
  have hd : (pair (w 17) (w 18))^2-(pair (w 1) (w 2))^2≠0 := by
    rw [hfV,hfU]
    intro hz
    have hr := congrArg QuadraticAlgebra.re hz
    norm_num [pair] at hr
    have hbad : (1:ℚ)=0 := by linear_combination -h39+w 78*hr
    norm_num at hbad
  have hh : ((pair (w 17) (w 18))^2-(pair (w 1) (w 2))^2)*RawAnchorNorm318.root w 0=
      pair (w 1) (w 2)*pair (w 19) (w 20)+pair (w 17) (w 18)*pair (w 3) (w 4) := by
    rw [hfV,hfU]
    change (pair (w 66) (2*w 67)-pair (1*w 58) (2*w 59))*pair (w 79) (w 80)=_
    ext <;> norm_num [pair] <;>
      [linear_combination h40;linear_combination h41]
  exact ⟨hu,hv,hd,hh⟩

theorem root0_point (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    RawAnchorNorm318.root w 0≠0 ∧
    E.Nonsingular ((RawAnchorNorm318.root w 0)^2)
      (RawAnchorNorm318.root w 0*RootPointAlgebra318.ordinateFactor
        (pair (w 1) (w 2)) (pair (w 3) (w 4)) (pair (w 17) (w 18)) (pair (w 19) (w 20))) := by
  obtain ⟨hu,hv,hd,hh⟩ := root0_data S w source
  exact RootPointAlgebra318.root_point _ _ _ _ _ hu hv hd hh

theorem root1_data (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (pair (w 7) (w 8))^2=1-D*(pair (w 5) (w 6))^4 ∧
    (pair (w 23) (w 24))^2=1-D*(pair (w 21) (w 22))^4 ∧
    (pair (w 21) (w 22))^2-(pair (w 5) (w 6))^2≠0 ∧
    ((pair (w 21) (w 22))^2-(pair (w 5) (w 6))^2)*RawAnchorNorm318.root w 1=
      pair (w 5) (w 6)*pair (w 23) (w 24)+pair (w 21) (w 22)*pair (w 7) (w 8) := by
  have h4 : r4 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=4)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r4] at h4
  have h5 : r5 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=5)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r5] at h5
  have h6 : r6 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=6)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r6] at h6
  have h7 : r7 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=7)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r7] at h7
  have h20 : r20 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=20)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r20] at h20
  have h21 : r21 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=21)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r21] at h21
  have h22 : r22 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=22)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r22] at h22
  have h23 : r23 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=23)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r23] at h23
  have h42 : r42 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=42)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r42] at h42
  have h43 : r43 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=43)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r43] at h43
  have h44 : r44 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=44)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r44] at h44
  have hfU : (pair (w 5) (w 6))^2=pair (1*w 60) (2*w 61) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -1*h4;linear_combination -2*h5]
  have hfV : (pair (w 21) (w 22))^2=pair (w 68) (2*w 69) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -h20;linear_combination -2*h21]
  have hu : (pair (w 7) (w 8))^2=1-D*(pair (w 5) (w 6))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfU]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h6;linear_combination h7]
  have hv : (pair (w 23) (w 24))^2=1-D*(pair (w 21) (w 22))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfV]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h22;linear_combination h23]
  have hd : (pair (w 21) (w 22))^2-(pair (w 5) (w 6))^2≠0 := by
    rw [hfV,hfU]
    intro hz
    have hr := congrArg QuadraticAlgebra.re hz
    norm_num [pair] at hr
    have hbad : (1:ℚ)=0 := by linear_combination -h42+w 81*hr
    norm_num at hbad
  have hh : ((pair (w 21) (w 22))^2-(pair (w 5) (w 6))^2)*RawAnchorNorm318.root w 1=
      pair (w 5) (w 6)*pair (w 23) (w 24)+pair (w 21) (w 22)*pair (w 7) (w 8) := by
    rw [hfV,hfU]
    change (pair (w 68) (2*w 69)-pair (1*w 60) (2*w 61))*pair (w 82) (w 83)=_
    ext <;> norm_num [pair] <;>
      [linear_combination h43;linear_combination h44]
  exact ⟨hu,hv,hd,hh⟩

theorem root1_point (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    RawAnchorNorm318.root w 1≠0 ∧
    E.Nonsingular ((RawAnchorNorm318.root w 1)^2)
      (RawAnchorNorm318.root w 1*RootPointAlgebra318.ordinateFactor
        (pair (w 5) (w 6)) (pair (w 7) (w 8)) (pair (w 21) (w 22)) (pair (w 23) (w 24))) := by
  obtain ⟨hu,hv,hd,hh⟩ := root1_data S w source
  exact RootPointAlgebra318.root_point _ _ _ _ _ hu hv hd hh

theorem root2_data (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (pair (w 11) (w 12))^2=1-D*(pair (w 9) (w 10))^4 ∧
    (pair (w 27) (w 28))^2=1-D*(pair (w 25) (w 26))^4 ∧
    (pair (w 25) (w 26))^2-(pair (w 9) (w 10))^2≠0 ∧
    ((pair (w 25) (w 26))^2-(pair (w 9) (w 10))^2)*RawAnchorNorm318.root w 2=
      pair (w 9) (w 10)*pair (w 27) (w 28)+pair (w 25) (w 26)*pair (w 11) (w 12) := by
  have h8 : r8 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=8)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r8] at h8
  have h9 : r9 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=9)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r9] at h9
  have h10 : r10 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=10)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r10] at h10
  have h11 : r11 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=11)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r11] at h11
  have h24 : r24 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=24)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r24] at h24
  have h25 : r25 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=25)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r25] at h25
  have h26 : r26 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=26)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r26] at h26
  have h27 : r27 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=27)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r27] at h27
  have h45 : r45 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=45)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r45] at h45
  have h46 : r46 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=46)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r46] at h46
  have h47 : r47 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=47)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r47] at h47
  have hfU : (pair (w 9) (w 10))^2=pair (2*w 62) (2*w 63) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -2*h8;linear_combination -2*h9]
  have hfV : (pair (w 25) (w 26))^2=pair (w 70) (2*w 71) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -h24;linear_combination -2*h25]
  have hu : (pair (w 11) (w 12))^2=1-D*(pair (w 9) (w 10))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfU]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h10;linear_combination h11]
  have hv : (pair (w 27) (w 28))^2=1-D*(pair (w 25) (w 26))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfV]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h26;linear_combination h27]
  have hd : (pair (w 25) (w 26))^2-(pair (w 9) (w 10))^2≠0 := by
    rw [hfV,hfU]
    intro hz
    have hr := congrArg QuadraticAlgebra.re hz
    norm_num [pair] at hr
    have hbad : (1:ℚ)=0 := by linear_combination -h45+w 84*hr
    norm_num at hbad
  have hh : ((pair (w 25) (w 26))^2-(pair (w 9) (w 10))^2)*RawAnchorNorm318.root w 2=
      pair (w 9) (w 10)*pair (w 27) (w 28)+pair (w 25) (w 26)*pair (w 11) (w 12) := by
    rw [hfV,hfU]
    change (pair (w 70) (2*w 71)-pair (2*w 62) (2*w 63))*pair (w 85) (w 86)=_
    ext <;> norm_num [pair] <;>
      [linear_combination h46;linear_combination h47]
  exact ⟨hu,hv,hd,hh⟩

theorem root2_point (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    RawAnchorNorm318.root w 2≠0 ∧
    E.Nonsingular ((RawAnchorNorm318.root w 2)^2)
      (RawAnchorNorm318.root w 2*RootPointAlgebra318.ordinateFactor
        (pair (w 9) (w 10)) (pair (w 11) (w 12)) (pair (w 25) (w 26)) (pair (w 27) (w 28))) := by
  obtain ⟨hu,hv,hd,hh⟩ := root2_data S w source
  exact RootPointAlgebra318.root_point _ _ _ _ _ hu hv hd hh

theorem root3_data (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (pair (w 15) (w 16))^2=1-D*(pair (w 13) (w 14))^4 ∧
    (pair (w 31) (w 32))^2=1-D*(pair (w 29) (w 30))^4 ∧
    (pair (w 29) (w 30))^2-(pair (w 13) (w 14))^2≠0 ∧
    ((pair (w 29) (w 30))^2-(pair (w 13) (w 14))^2)*RawAnchorNorm318.root w 3=
      pair (w 13) (w 14)*pair (w 31) (w 32)+pair (w 29) (w 30)*pair (w 15) (w 16) := by
  have h12 : r12 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=12)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r12] at h12
  have h13 : r13 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=13)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r13] at h13
  have h14 : r14 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=14)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r14] at h14
  have h15 : r15 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=15)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r15] at h15
  have h28 : r28 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=28)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r28] at h28
  have h29 : r29 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=29)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r29] at h29
  have h30 : r30 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=30)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r30] at h30
  have h31 : r31 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=31)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r31] at h31
  have h48 : r48 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=48)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r48] at h48
  have h49 : r49 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=49)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r49] at h49
  have h50 : r50 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=50)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r50] at h50
  have hfU : (pair (w 13) (w 14))^2=pair (1*w 64) (2*w 65) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -1*h12;linear_combination -2*h13]
  have hfV : (pair (w 29) (w 30))^2=pair (w 72) (2*w 73) := by
    ext <;> norm_num [pair,pow_two] <;>
      [linear_combination -h28;linear_combination -2*h29]
  have hu : (pair (w 15) (w 16))^2=1-D*(pair (w 13) (w 14))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfU]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h14;linear_combination h15]
  have hv : (pair (w 31) (w 32))^2=1-D*(pair (w 29) (w 30))^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hfV]
    ext <;> norm_num [D,i,pair,pow_succ] <;>
      [linear_combination h30;linear_combination h31]
  have hd : (pair (w 29) (w 30))^2-(pair (w 13) (w 14))^2≠0 := by
    rw [hfV,hfU]
    intro hz
    have hr := congrArg QuadraticAlgebra.re hz
    norm_num [pair] at hr
    have hbad : (1:ℚ)=0 := by linear_combination -h48+w 87*hr
    norm_num at hbad
  have hh : ((pair (w 29) (w 30))^2-(pair (w 13) (w 14))^2)*RawAnchorNorm318.root w 3=
      pair (w 13) (w 14)*pair (w 31) (w 32)+pair (w 29) (w 30)*pair (w 15) (w 16) := by
    rw [hfV,hfU]
    change (pair (w 72) (2*w 73)-pair (1*w 64) (2*w 65))*pair (w 88) (w 89)=_
    ext <;> norm_num [pair] <;>
      [linear_combination h49;linear_combination h50]
  exact ⟨hu,hv,hd,hh⟩

theorem root3_point (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    RawAnchorNorm318.root w 3≠0 ∧
    E.Nonsingular ((RawAnchorNorm318.root w 3)^2)
      (RawAnchorNorm318.root w 3*RootPointAlgebra318.ordinateFactor
        (pair (w 13) (w 14)) (pair (w 15) (w 16)) (pair (w 29) (w 30)) (pair (w 31) (w 32))) := by
  obtain ⟨hu,hv,hd,hh⟩ := root3_data S w source
  exact RootPointAlgebra318.root_point _ _ _ _ _ hu hv hd hh


theorem all_root_factors (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ∀i:Fin 4,∃j:K,j^2=(RawAnchorNorm318.root w i)^4-D ∧ RawAnchorNorm318.root w i≠0 := by
  intro i
  fin_cases i
  · obtain ⟨hu,hv,hd,hh⟩ := root0_data S w source
    refine ⟨RootPointAlgebra318.ordinateFactor (pair (w 1) (w 2)) (pair (w 3) (w 4)) (pair (w 17) (w 18)) (pair (w 19) (w 20)),?_,(root0_point S w source).1⟩
    exact RootPointAlgebra318.root_factor_curve _ _ _ _ _ hu hv hd hh
  · obtain ⟨hu,hv,hd,hh⟩ := root1_data S w source
    refine ⟨RootPointAlgebra318.ordinateFactor (pair (w 5) (w 6)) (pair (w 7) (w 8)) (pair (w 21) (w 22)) (pair (w 23) (w 24)),?_,(root1_point S w source).1⟩
    exact RootPointAlgebra318.root_factor_curve _ _ _ _ _ hu hv hd hh
  · obtain ⟨hu,hv,hd,hh⟩ := root2_data S w source
    refine ⟨RootPointAlgebra318.ordinateFactor (pair (w 9) (w 10)) (pair (w 11) (w 12)) (pair (w 25) (w 26)) (pair (w 27) (w 28)),?_,(root2_point S w source).1⟩
    exact RootPointAlgebra318.root_factor_curve _ _ _ _ _ hu hv hd hh
  · obtain ⟨hu,hv,hd,hh⟩ := root3_data S w source
    refine ⟨RootPointAlgebra318.ordinateFactor (pair (w 13) (w 14)) (pair (w 15) (w 16)) (pair (w 29) (w 30)) (pair (w 31) (w 32)),?_,(root3_point S w source).1⟩
    exact RootPointAlgebra318.root_factor_curve _ _ _ _ _ hu hv hd hh

end RawRootPoints318
