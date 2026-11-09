module
public import CompressedChartDomains318
public import CoherentMultiplePrefix318
public section
noncomputable section
namespace PadeRatioWitness318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay
open CompressedOrientation318 (k m D shift mid fV)
open Pade21Domains
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def u (w : Assignment) (j : Fin 8) : K := pair (w (4*j.val+1)) (w (4*j.val+2))
@[expose] def v (w : Assignment) (j : Fin 8) : K := pair (w (4*j.val+3)) (w (4*j.val+4))
@[expose] def A (w : Assignment) : K := m+k^2*shift w+D*mid w
@[expose] def B (w : Assignment) : K := k^2+m*shift w+D*fV w
@[expose] def arg (w : Assignment) : K := D*(fV w)^2

structure Data where
  commonPolynomial : K
  commonLog : K
  alternatePolynomial : Fin 4 → K
  primaryRatio : Fin 4 → K
  alternateRatio : Fin 4 → K

/-- These are exact field identities of the rational formulas, not assumed
source-row witnesses. The constructor below proves all of them by division. -/
def Relations (w : Assignment) (z : Data) : Prop :=
  QG (arg w)*z.commonPolynomial=PG (arg w) ∧
  B w*z.commonLog=k*shift w*z.commonPolynomial ∧
  z.alternatePolynomial 0=1-(v w 4-1)/5 ∧
  (∀ j : Fin 3, QJ (v w ⟨j.val+5,by omega⟩-1)*z.alternatePolynomial ⟨j.val+1,by omega⟩=
    PJ (v w ⟨j.val+5,by omega⟩-1)) ∧
  (∀ j : Fin 4, k*v w (j.castAdd 4)* z.primaryRatio j=u w (j.castAdd 4)*A w) ∧
  (∀ j : Fin 4, z.commonLog*z.alternateRatio j=
    -u w (j.natAdd 4)*z.alternatePolynomial j)

@[expose] def fill (w : Assignment) (z : Data) : Assignment := fun i => match i with
  | 90 => ((fV w)^2).re
  | 91 => (fV w).re*(fV w).im
  | 92 => z.commonPolynomial.re
  | 93 => z.commonPolynomial.im
  | 94 => z.commonLog.re
  | 95 => z.commonLog.im
  | 96 => (z.alternatePolynomial 1).re
  | 97 => (z.alternatePolynomial 1).im
  | 98 => (z.alternatePolynomial 2).re
  | 99 => (z.alternatePolynomial 2).im
  | 100 => (z.alternatePolynomial 3).re
  | 101 => (z.alternatePolynomial 3).im
  | 102 => (z.primaryRatio 0).re
  | 103 => (z.primaryRatio 0).im
  | 104 => (z.alternateRatio 0).re
  | 105 => (z.alternateRatio 0).im
  | 106 => (z.primaryRatio 1).re
  | 107 => (z.primaryRatio 1).im
  | 108 => (z.alternateRatio 1).re
  | 109 => (z.alternateRatio 1).im
  | 110 => (z.primaryRatio 2).re
  | 111 => (z.primaryRatio 2).im
  | 112 => (z.alternateRatio 2).re
  | 113 => (z.alternateRatio 2).im
  | 114 => (z.primaryRatio 3).re
  | 115 => (z.primaryRatio 3).im
  | 116 => (z.alternateRatio 3).re
  | 117 => (z.alternateRatio 3).im
  | i => w i

lemma fill_input (w : Assignment) (z : Data) : fill w z 0=w 0 := rfl

lemma preserves_first51 (S : ℚ) (w : Assignment) (z : Data)
    (hw : Constraints ((stage0 S).take 51) w) :
    Constraints ((stage0 S).take 51) (fill w z) := by
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S] w at hw
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S] (fill w z)
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
  simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,fill] using hw

@[expose] def rows (S : ℚ) := [r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S]

theorem literal_rows (S : ℚ) (w : Assignment) (z : Data) (hz : Relations w z) :
    Constraints (rows S) (fill w z) := by
  obtain ⟨hp,hc,hfirst,hj,hl,hr⟩ := hz
  have h51 : r51 S (fill w z)=0 := by
    simp [r51,fill,fV,pair,pow_two] <;> ring
  have h52 : r52 S (fill w z)=0 := by
    simp [r52,fill,fV,pair,pow_two]
  have e53 := hp
  have h53 : r53 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e53
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r53,fill,fV,pair,pow_two]
    linear_combination he
  have h54 : r54 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e53
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r54,fill,fV,pair,pow_two]
    linear_combination he
  have e55 := hc
  have h55 : r55 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e55
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r55,fill,fV,pair,pow_two]
    linear_combination he
  have h56 : r56 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e55
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r56,fill,fV,pair,pow_two]
    linear_combination he
  have e57 := hj 0
  have h57 : r57 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e57
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r57,fill,fV,pair,pow_two]
    linear_combination he
  have h58 : r58 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e57
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r58,fill,fV,pair,pow_two]
    linear_combination he
  have e59 := hj 1
  have h59 : r59 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e59
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r59,fill,fV,pair,pow_two]
    linear_combination he
  have h60 : r60 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e59
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r60,fill,fV,pair,pow_two]
    linear_combination he
  have e61 := hj 2
  have h61 : r61 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e61
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r61,fill,fV,pair,pow_two]
    linear_combination he
  have h62 : r62 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e61
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r62,fill,fV,pair,pow_two]
    linear_combination he
  have e63 := hl 0
  have h63 : r63 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e63
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r63,fill,fV,pair,pow_two]
    linear_combination he
  have h64 : r64 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e63
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r64,fill,fV,pair,pow_two]
    linear_combination he
  have e65 := hr 0
  rw [hfirst] at e65
  have h65 : r65 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e65
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r65,fill,fV,pair,pow_two]
    linear_combination he
  have h66 : r66 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e65
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r66,fill,fV,pair,pow_two]
    linear_combination he
  have e67 := hl 1
  have h67 : r67 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e67
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r67,fill,fV,pair,pow_two]
    linear_combination he
  have h68 : r68 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e67
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r68,fill,fV,pair,pow_two]
    linear_combination he
  have e69 := hr 1
  have h69 : r69 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e69
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r69,fill,fV,pair,pow_two]
    linear_combination he
  have h70 : r70 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e69
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r70,fill,fV,pair,pow_two]
    linear_combination he
  have e71 := hl 2
  have h71 : r71 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e71
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r71,fill,fV,pair,pow_two]
    linear_combination he
  have h72 : r72 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e71
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r72,fill,fV,pair,pow_two]
    linear_combination he
  have e73 := hr 2
  have h73 : r73 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e73
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r73,fill,fV,pair,pow_two]
    linear_combination he
  have h74 : r74 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e73
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r74,fill,fV,pair,pow_two]
    linear_combination he
  have e75 := hl 3
  have h75 : r75 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e75
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r75,fill,fV,pair,pow_two]
    linear_combination he
  have h76 : r76 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e75
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r76,fill,fV,pair,pow_two]
    linear_combination he
  have e77 := hr 3
  have h77 : r77 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.re e77
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r77,fill,fV,pair,pow_two]
    linear_combination he
  have h78 : r78 S (fill w z)=0 := by
    have he := congrArg QuadraticAlgebra.im e77
    norm_num [QG,PG,QJ,PJ,arg,A,B,u,v,shift,mid,fV,k,m,D,pair,pow_two,QuadraticAlgebra.norm_def] at he
    norm_num [r78,fill,fV,pair,pow_two]
    linear_combination he
  simp [Constraints,rows,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78]

theorem first79 (S : ℚ) (w : Assignment) (z : Data)
    (hw : Constraints ((stage0 S).take 51) w) (hz : Relations w z) :
    Constraints ((stage0 S).take 79) (fill w z) := by
  change Constraints (((stage0 S).take 51) ++ rows S) _
  exact (constraints_append _ _ _).mpr ⟨preserves_first51 S w z hw,literal_rows S w z hz⟩

end PadeRatioWitness318
