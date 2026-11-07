module
public import CompressedGlobal318
public import Pade21Domains
public section
namespace RawAlternatePade318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318
open CompressedPoint318 CompressedGlobal318 Pade21Domains
open scoped QuadraticAlgebra
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
noncomputable section

@[expose] def d : K := pair 3 (-1)
theorem d_square : d^2=D := by ext <;> norm_num [d,D,pair,pow_two,QuadraticAlgebra.norm_def]
@[expose] def argument (w : Assignment) : K := pair (11*w 90-24*w 91) (-6*w 90+22*w 91)
@[expose] def polynomial0 (w : Assignment) : K := pair (w 92) (w 93)
@[expose] def commonLog (w : Assignment) : K := pair (w 94) (w 95)

theorem source_argument (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    argument w=D*(fV w)^2 := by
  have h51 : r51 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=51) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r51] at h51
  have h52 : r52 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=52) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r52] at h52
  ext <;> norm_num [argument,D,fV,pair,pow_two,QuadraticAlgebra.norm_def]
  · linear_combination 11*h51-24*h52
  · linear_combination -6*h51+22*h52

theorem source_polynomial0 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    QG (argument w)*polynomial0 w=PG (argument w) := by
  have h53 : r53 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=53) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r53] at h53
  have h54 : r54 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=54) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r54] at h54
  ext <;> norm_num [QG,PG,argument,polynomial0,pair,pow_two,QuadraticAlgebra.norm_def]
  · linear_combination h53
  · linear_combination h54

theorem source_commonLog (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    anchorB w*commonLog w=k*shift w*polynomial0 w := by
  have h55 : r55 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=55) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r55] at h55
  have h56 : r56 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=56) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r56] at h56
  ext <;> norm_num [anchorB,commonLog,k,m,D,shift,fV,polynomial0,pair,pow_two,QuadraticAlgebra.norm_def]
  · linear_combination h55
  · linear_combination h56

theorem source_commonLog_eq (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    commonLog w=zV w*polynomial0 w := by
  have hh := source_commonLog S w source
  have hB := source_B_ne S w source
  dsimp [zV]
  field_simp [hB]
  linear_combination hh

theorem source_polynomial0_eq (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial0 w=PG (D*(fV w)^2)/QG (D*(fV w)^2) := by
  have hx : D*(fV w)^2=(d*fV w)^2 := by rw [mul_pow,d_square]
  have hQ := QG_nonzero_on_square (d*fV w)
  rw [←hx] at hQ
  apply (eq_div_iff hQ).mpr
  have hh := source_polynomial0 S w source
  rw [source_argument S w source] at hh
  simpa [mul_comm] using hh

theorem source_commonLog_zero (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    commonLog w=0 ↔ shift w=0 := by
  have hp : polynomial0 w≠0 := by
    have hh := source_polynomial0 S w source
    intro hz
    rw [hz,mul_zero] at hh
    exact PG_nonzero (argument w) hh.symm
  rw [source_commonLog_eq S w source,mul_eq_zero]
  simp only [hp,or_false,source_zV_zero S w source]

@[expose] def u1 (w : Assignment) : K := pair (w 17) (w 18)
@[expose] def v1 (w : Assignment) : K := pair (w 19) (w 20)
@[expose] def delta1 (w : Assignment) : K := v1 w-1
@[expose] def polynomial1 (w : Assignment) : K := 1-(delta1 w)/5
@[expose] def rawRatio1 (w : Assignment) : K := pair (w 104) (w 105)

theorem source_curve1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v1 w)^2+(d*(u1 w)^2)^2=1 := by
  have hh := RawReciprocal318.VA_curve S w source
  change (v1 w)^2=1-D*(u1 w)^4 at hh
  rw [mul_pow,d_square]
  linear_combination hh

theorem source_polynomial1_ne (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial1 w≠0 := by
  intro hp
  have hv : v1 w=6 := by dsimp [polynomial1,delta1] at hp; linear_combination -5*hp
  have hc := source_curve1 S w source
  rw [hv] at hc
  apply square_not_negative (-35) (by norm_num) (d*(u1 w)^2)
  norm_num at hc ⊢
  linear_combination hc

theorem source_ratio1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    commonLog w*rawRatio1 w= -u1 w*polynomial1 w := by
  have h65 : r65 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=65) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r65] at h65
  have h66 : r66 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=66) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r66] at h66
  ext <;> norm_num [commonLog,rawRatio1,u1,polynomial1,delta1,v1,pair,QuadraticAlgebra.norm_def]
  · linear_combination h65
  · linear_combination h66

theorem source_identity_branch1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w=0) : u1 w=0 := by
  have hc := (source_commonLog_zero S w source).mpr hs
  have hh := source_ratio1 S w source
  rw [hc,zero_mul] at hh
  exact neg_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_right (source_polynomial1_ne S w source))

@[expose] def u2 (w : Assignment) : K := pair (w 21) (w 22)
@[expose] def v2 (w : Assignment) : K := pair (w 23) (w 24)
@[expose] def delta2 (w : Assignment) : K := v2 w-1
@[expose] def polynomial2 (w : Assignment) : K := pair (w 96) (w 97)
@[expose] def rawRatio2 (w : Assignment) : K := pair (w 108) (w 109)

theorem source_curve2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v2 w)^2+(d*(u2 w)^2)^2=1 := by
  have hh := RawReciprocal318.VS_curve S w source
  change (v2 w)^2=1-D*(u2 w)^4 at hh
  rw [mul_pow,d_square]
  linear_combination hh

theorem source_polynomial2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    QJ (delta2 w)*polynomial2 w=PJ (delta2 w) := by
  have h57 : r57 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=57) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r57] at h57
  have h58 : r58 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=58) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r58] at h58
  ext <;> norm_num [QJ,PJ,delta2,v2,polynomial2,pair,pow_two,QuadraticAlgebra.norm_def]
  · linear_combination h57
  · linear_combination h58

theorem source_polynomial2_eq (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial2 w=PJ (delta2 w)/QJ (delta2 w) := by
  have hQ := QJ_nonzero_on_circle (v2 w) (d*(u2 w)^2) (source_curve2 S w source)
  apply (eq_div_iff hQ).mpr
  simpa [mul_comm,delta2] using source_polynomial2 S w source

theorem source_polynomial2_ne (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial2 w≠0 := by
  have hh := source_polynomial2 S w source
  intro hz
  rw [hz,mul_zero] at hh
  exact PJ_nonzero (delta2 w) hh.symm

theorem source_ratio2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    commonLog w*rawRatio2 w= -u2 w*polynomial2 w := by
  have h69 : r69 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=69) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r69] at h69
  have h70 : r70 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=70) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r70] at h70
  ext <;> norm_num [commonLog,rawRatio2,u2,polynomial2,pair,QuadraticAlgebra.norm_def]
  · linear_combination h69
  · linear_combination h70

theorem source_identity_branch2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w=0) : u2 w=0 := by
  have hc := (source_commonLog_zero S w source).mpr hs
  have hh := source_ratio2 S w source
  rw [hc,zero_mul] at hh
  exact neg_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_right (source_polynomial2_ne S w source))

@[expose] def u3 (w : Assignment) : K := pair (w 25) (w 26)
@[expose] def v3 (w : Assignment) : K := pair (w 27) (w 28)
@[expose] def delta3 (w : Assignment) : K := v3 w-1
@[expose] def polynomial3 (w : Assignment) : K := pair (w 98) (w 99)
@[expose] def rawRatio3 (w : Assignment) : K := pair (w 112) (w 113)

theorem source_curve3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v3 w)^2+(d*(u3 w)^2)^2=1 := by
  have hh := RawReciprocal318.VT_curve S w source
  change (v3 w)^2=1-D*(u3 w)^4 at hh
  rw [mul_pow,d_square]
  linear_combination hh

theorem source_polynomial3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    QJ (delta3 w)*polynomial3 w=PJ (delta3 w) := by
  have h59 : r59 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=59) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r59] at h59
  have h60 : r60 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=60) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r60] at h60
  ext <;> norm_num [QJ,PJ,delta3,v3,polynomial3,pair,pow_two,QuadraticAlgebra.norm_def]
  · linear_combination h59
  · linear_combination h60

theorem source_polynomial3_eq (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial3 w=PJ (delta3 w)/QJ (delta3 w) := by
  have hQ := QJ_nonzero_on_circle (v3 w) (d*(u3 w)^2) (source_curve3 S w source)
  apply (eq_div_iff hQ).mpr
  simpa [mul_comm,delta3] using source_polynomial3 S w source

theorem source_polynomial3_ne (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial3 w≠0 := by
  have hh := source_polynomial3 S w source
  intro hz
  rw [hz,mul_zero] at hh
  exact PJ_nonzero (delta3 w) hh.symm

theorem source_ratio3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    commonLog w*rawRatio3 w= -u3 w*polynomial3 w := by
  have h73 : r73 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=73) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r73] at h73
  have h74 : r74 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=74) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r74] at h74
  ext <;> norm_num [commonLog,rawRatio3,u3,polynomial3,pair,QuadraticAlgebra.norm_def]
  · linear_combination h73
  · linear_combination h74

theorem source_identity_branch3 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w=0) : u3 w=0 := by
  have hc := (source_commonLog_zero S w source).mpr hs
  have hh := source_ratio3 S w source
  rw [hc,zero_mul] at hh
  exact neg_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_right (source_polynomial3_ne S w source))

@[expose] def u4 (w : Assignment) : K := pair (w 29) (w 30)
@[expose] def v4 (w : Assignment) : K := pair (w 31) (w 32)
@[expose] def delta4 (w : Assignment) : K := v4 w-1
@[expose] def polynomial4 (w : Assignment) : K := pair (w 100) (w 101)
@[expose] def rawRatio4 (w : Assignment) : K := pair (w 116) (w 117)

theorem source_curve4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (v4 w)^2+(d*(u4 w)^2)^2=1 := by
  have hh := RawReciprocal318.VZ_curve S w source
  change (v4 w)^2=1-D*(u4 w)^4 at hh
  rw [mul_pow,d_square]
  linear_combination hh

theorem source_polynomial4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    QJ (delta4 w)*polynomial4 w=PJ (delta4 w) := by
  have h61 : r61 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=61) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r61] at h61
  have h62 : r62 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=62) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r62] at h62
  ext <;> norm_num [QJ,PJ,delta4,v4,polynomial4,pair,pow_two,QuadraticAlgebra.norm_def]
  · linear_combination h61
  · linear_combination h62

theorem source_polynomial4_eq (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial4 w=PJ (delta4 w)/QJ (delta4 w) := by
  have hQ := QJ_nonzero_on_circle (v4 w) (d*(u4 w)^2) (source_curve4 S w source)
  apply (eq_div_iff hQ).mpr
  simpa [mul_comm,delta4] using source_polynomial4 S w source

theorem source_polynomial4_ne (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    polynomial4 w≠0 := by
  have hh := source_polynomial4 S w source
  intro hz
  rw [hz,mul_zero] at hh
  exact PJ_nonzero (delta4 w) hh.symm

theorem source_ratio4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    commonLog w*rawRatio4 w= -u4 w*polynomial4 w := by
  have h77 : r77 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=77) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r77] at h77
  have h78 : r78 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=78) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r78] at h78
  ext <;> norm_num [commonLog,rawRatio4,u4,polynomial4,pair,QuadraticAlgebra.norm_def]
  · linear_combination h77
  · linear_combination h78

theorem source_identity_branch4 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w=0) : u4 w=0 := by
  have hc := (source_commonLog_zero S w source).mpr hs
  have hh := source_ratio4 S w source
  rw [hc,zero_mul] at hh
  exact neg_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_right (source_polynomial4_ne S w source))

theorem source_shift_nonzero_at_contact (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hf : 0<v (fH w)) : shift w≠0 := by
  intro hs
  obtain ⟨ht,hg⟩ := source_products S w source
  have he := (source_relations S w source).2
  rw [ht,hg,hs] at he
  simp only [mul_zero,zero_pow (by decide : 2≠0),add_zero] at he
  have hh := congrArg v he
  simp only [v.map_one,v.map_mul,v.map_pow,hk,nsmul_zero,zero_add] at hh
  rw [←hh] at hf
  exact lt_irrefl _ hf

theorem source_commonLog_ne_at_contact (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hf : 0<v (fH w)) : commonLog w≠0 := by
  intro hz
  exact source_shift_nonzero_at_contact S w source v hk hf
    ((source_commonLog_zero S w source).mp hz)

theorem source_ratio1_eq_at_contact (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hf : 0<v (fH w)) :
    rawRatio1 w=(-u1 w*polynomial1 w)/commonLog w := by
  apply (eq_div_iff (source_commonLog_ne_at_contact S w source v hk hf)).mpr
  simpa [mul_comm] using source_ratio1 S w source

theorem source_ratio2_eq_at_contact (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hf : 0<v (fH w)) :
    rawRatio2 w=(-u2 w*polynomial2 w)/commonLog w := by
  apply (eq_div_iff (source_commonLog_ne_at_contact S w source v hk hf)).mpr
  simpa [mul_comm] using source_ratio2 S w source

theorem source_ratio3_eq_at_contact (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hf : 0<v (fH w)) :
    rawRatio3 w=(-u3 w*polynomial3 w)/commonLog w := by
  apply (eq_div_iff (source_commonLog_ne_at_contact S w source v hk hf)).mpr
  simpa [mul_comm] using source_ratio3 S w source

theorem source_ratio4_eq_at_contact (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hf : 0<v (fH w)) :
    rawRatio4 w=(-u4 w*polynomial4 w)/commonLog w := by
  apply (eq_div_iff (source_commonLog_ne_at_contact S w source v hk hf)).mpr
  simpa [mul_comm] using source_ratio4 S w source

end
end RawAlternatePade318
