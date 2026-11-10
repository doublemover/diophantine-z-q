module
public import Source107CRTWitness318
public section
noncomputable section
namespace ContactWeightWitness318
open CircuitReplay Raw318FinalReplay
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact five contact roots of the original source, in its original
normalization. t remains free for the subsequent prime-pattern choice. -/
@[expose] def contact (t : ℚ) : ℚ := t*(t+1/2)*(t+1)*(t-1/2399)*(t+32/407)
@[expose] def weight (t : ℚ) : ℚ := (t-1)^2/contact t

lemma contact_ne (t : ℚ) (h0 : t≠0) (h1 : t≠ -1/2) (h2 : t≠ -1)
    (h3 : t≠1/2399) (h4 : t≠ -32/407) : contact t≠0 := by
  unfold contact
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0
    (by intro he; apply h1; linarith)) (by intro he; apply h2; linarith))
    (sub_ne_zero.mpr h3)) (by intro he; apply h4; linarith)

lemma weight_ne (t : ℚ) (hF : contact t≠0) (h1 : t≠1) : weight t≠0 :=
  div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr h1)) hF

/-- Actual source weights are explicit monomials in q and delta. This
avoids treating later division equations as supplied witnesses. -/
@[expose] def fill (w : Assignment) (t : ℚ) : Assignment := fun i => match i with
  | 38 => t
  | 146 => 1/t
  | 147 => t^2
  | 148 => t^3
  | 149 => t^4+(1952786/3081901)*t^5+(1205412/3081901)*t^3
  | 150 => t^3-2*t^2
  | 151 => weight t
  | 152 => -weight t*((t-1)^3+1)
  | 153 => -t*weight t*(t-1)^3
  | 154 => (weight t)^2*(t-1)^6
  | 155 => (weight t)^4*(t-1)^11
  | 156 => (weight t)^7*(t-1)^18
  | 157 => (weight t)^13*(t-1)^36
  | 158 => (weight t)^25*(t-1)^72
  | i => w i

lemma fill_input (w : Assignment) (t : ℚ) : fill w t 0=w 0 := rfl

lemma preserves_first107 (S : ℚ) (w : Assignment) (t : ℚ)
    (hw : Constraints ((stage0 S).take 107) w) :
    Constraints ((stage0 S).take 107) (fill w t) := by
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S] w at hw
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S] (fill w t)
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
  simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,fill] using hw

@[expose] def rows (S : ℚ) := [r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S]

theorem literal_rows (S : ℚ) (w : Assignment) (t : ℚ) (ht : t≠0) (hF : contact t≠0) :
    Constraints (rows S) (fill w t) := by
  have hq : contact t*weight t=(t-1)^2 := by
    unfold weight
    field_simp [hF]
  have h107 : r107 S (fill w t)=0 := by simp [r107,fill,ht]
  have h108 : r108 S (fill w t)=0 := by simp only [r108,fill]; ring
  have h109 : r109 S (fill w t)=0 := by simp only [r109,fill]; ring
  have h110 : r110 S (fill w t)=0 := by simp only [r110,fill]; ring
  have h111 : r111 S (fill w t)=0 := by simp only [r111,fill]; ring
  have h112 : r112 S (fill w t)=0 := by
    dsimp [r112,fill]
    unfold contact at hq
    generalize weight t = Q at hq ⊢
    linear_combination hq
  have h113 : r113 S (fill w t)=0 := by simp only [r113,fill]; ring
  have h114 : r114 S (fill w t)=0 := by simp only [r114,fill]; ring
  have h115 : r115 S (fill w t)=0 := by simp only [r115,fill]; ring
  have h116 : r116 S (fill w t)=0 := by simp only [r116,fill]; ring
  have h117 : r117 S (fill w t)=0 := by simp only [r117,fill]; ring
  have h118 : r118 S (fill w t)=0 := by simp only [r118,fill]; ring
  have h119 : r119 S (fill w t)=0 := by simp only [r119,fill]; ring
  simp [Constraints,rows,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119]

theorem first120 (S : ℚ) (w : Assignment) (t : ℚ)
    (ht : t≠0) (hF : contact t≠0) (hw : Constraints ((stage0 S).take 107) w) :
    Constraints ((stage0 S).take 120) (fill w t) := by
  change Constraints (((stage0 S).take 107) ++ rows S) _
  exact (constraints_append _ _ _).mpr ⟨preserves_first107 S w t hw,literal_rows S w t ht hF⟩

end ContactWeightWitness318
