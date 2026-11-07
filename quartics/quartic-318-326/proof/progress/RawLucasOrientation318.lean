module
public import CompressedOrientation318
public section
namespace RawLucasOrientation318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay RawDetector318 CompressedOrientation318
open scoped QuadraticAlgebra
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

@[expose] def anchorA (w : Assignment) : K := m+k^2*shift w+D*mid w

@[expose] def u1 (w : Assignment) : K := pair (w 1) (w 2)
@[expose] def v1 (w : Assignment) : K := pair (w 3) (w 4)
@[expose] def L1 (w : Assignment) : K := pair (w 102) (w 103)
theorem curve1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v1 w)^2=1-D*(u1 w)^4 := by
  have h0 : r0 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=0) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h1 : r1 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=1) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h2 : r2 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=2) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h3 : r3 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=3) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr : w 58=((w 1)^2+2*(w 2)^2) := by dsimp only [r0] at h0; nlinarith
  have hi : w 59=w 1*w 2 := by dsimp only [r1] at h1; nlinarith
  dsimp only [r2] at h2
  dsimp only [r3] at h3
  rw [hr,hi] at h2 h3
  ext <;> norm_num [u1,v1,D,pair,pow_succ]
  · linear_combination h2
  · linear_combination h3

theorem ratio1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    k*v1 w*L1 w=u1 w*anchorA w := by
  have h63 : r63 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=63) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h64 : r64 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=64) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [k,m,D,shift,mid,u1,v1,L1,anchorA,pair,pow_two]
  · dsimp only [r63] at h63; linear_combination h63
  · dsimp only [r64] at h64; linear_combination h64

@[expose] def u2 (w : Assignment) : K := pair (w 5) (w 6)
@[expose] def v2 (w : Assignment) : K := pair (w 7) (w 8)
@[expose] def L2 (w : Assignment) : K := pair (w 106) (w 107)
theorem curve2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v2 w)^2=1-D*(u2 w)^4 := by
  have h4 : r4 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=4) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h5 : r5 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=5) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h6 : r6 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=6) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h7 : r7 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=7) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr : w 60=((w 5)^2+2*(w 6)^2) := by dsimp only [r4] at h4; nlinarith
  have hi : w 61=w 5*w 6 := by dsimp only [r5] at h5; nlinarith
  dsimp only [r6] at h6
  dsimp only [r7] at h7
  rw [hr,hi] at h6 h7
  ext <;> norm_num [u2,v2,D,pair,pow_succ]
  · linear_combination h6
  · linear_combination h7

theorem ratio2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    k*v2 w*L2 w=u2 w*anchorA w := by
  have h67 : r67 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=67) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h68 : r68 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=68) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [k,m,D,shift,mid,u2,v2,L2,anchorA,pair,pow_two]
  · dsimp only [r67] at h67; linear_combination h67
  · dsimp only [r68] at h68; linear_combination h68

@[expose] def u3 (w : Assignment) : K := pair (w 9) (w 10)
@[expose] def v3 (w : Assignment) : K := pair (w 11) (w 12)
@[expose] def L3 (w : Assignment) : K := pair (w 110) (w 111)
theorem curve3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v3 w)^2=1-D*(u3 w)^4 := by
  have h8 : r8 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=8) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h9 : r9 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=9) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h10 : r10 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=10) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h11 : r11 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=11) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr : w 62=((w 9)^2+2*(w 10)^2) /2 := by dsimp only [r8] at h8; nlinarith
  have hi : w 63=w 9*w 10 := by dsimp only [r9] at h9; nlinarith
  dsimp only [r10] at h10
  dsimp only [r11] at h11
  rw [hr,hi] at h10 h11
  ext <;> norm_num [u3,v3,D,pair,pow_succ]
  · linear_combination h10
  · linear_combination h11

theorem ratio3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    k*v3 w*L3 w=u3 w*anchorA w := by
  have h71 : r71 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=71) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h72 : r72 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=72) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [k,m,D,shift,mid,u3,v3,L3,anchorA,pair,pow_two]
  · dsimp only [r71] at h71; linear_combination h71
  · dsimp only [r72] at h72; linear_combination h72

@[expose] def u4 (w : Assignment) : K := pair (w 13) (w 14)
@[expose] def v4 (w : Assignment) : K := pair (w 15) (w 16)
@[expose] def L4 (w : Assignment) : K := pair (w 114) (w 115)
theorem curve4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v4 w)^2=1-D*(u4 w)^4 := by
  have h12 : r12 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=12) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h13 : r13 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=13) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h14 : r14 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=14) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h15 : r15 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=15) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr : w 64=((w 13)^2+2*(w 14)^2) := by dsimp only [r12] at h12; nlinarith
  have hi : w 65=w 13*w 14 := by dsimp only [r13] at h13; nlinarith
  dsimp only [r14] at h14
  dsimp only [r15] at h15
  rw [hr,hi] at h14 h15
  ext <;> norm_num [u4,v4,D,pair,pow_succ]
  · linear_combination h14
  · linear_combination h15

theorem ratio4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    k*v4 w*L4 w=u4 w*anchorA w := by
  have h75 : r75 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=75) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h76 : r76 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=76) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  ext <;> norm_num [k,m,D,shift,mid,u4,v4,L4,anchorA,pair,pow_two]
  · dsimp only [r75] at h75; linear_combination h75
  · dsimp only [r76] at h76; linear_combination h76

theorem lucas_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    test15 S w=(L3 w)^2-L2 w*(L2 w-2)*L3 w*L4 w+(L2 w-2)^2*(L4 w)^2-1 := by
  have h80 : r80 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=80) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h81 : r81 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=81) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h82 : r82 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=82) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h83 : r83 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=83) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h84 : r84 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=84) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h85 : r85 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=85) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h119 : w 119=w 106*w 114+2*w 107*w 115 := by dsimp only [r80] at h80; linear_combination h80
  have h120 : w 120=w 106*w 115+w 107*w 114 := by dsimp only [r81] at h81; linear_combination h81
  have h121 : w 121=w 106*w 110+2*w 107*w 111 := by dsimp only [r82] at h82; linear_combination h82
  have h122 : w 122=w 106*w 111+w 107*w 110 := by dsimp only [r83] at h83; linear_combination h83
  dsimp only [r84] at h84
  dsimp only [r85] at h85
  rw [h119,h120,h121,h122] at h84 h85
  ext <;> norm_num [test15,L2,L3,L4,pair,pow_two]
  · linear_combination h84
  · linear_combination 2*h85


theorem source_products (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    mid w=fH w*shift w ∧ fV w=fH w*(shift w)^2 := by
  have h32 : r32 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=32) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h33 : r33 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=33) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h34 : r34 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=34) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h35 : r35 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=35) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have ht : mid w=fH w*shift w := by
    ext <;> norm_num [mid,fH,shift,pair]
    · dsimp only [r32] at h32; linear_combination h32
    · dsimp only [r33] at h33; linear_combination h33
  have hg : fV w=mid w*shift w := by
    ext <;> norm_num [fV,mid,shift,pair]
    · dsimp only [r34] at h34; linear_combination h34
    · dsimp only [r35] at h35; linear_combination h35
  exact ⟨ht,by rw [hg,ht]; ring⟩

end RawLucasOrientation318
