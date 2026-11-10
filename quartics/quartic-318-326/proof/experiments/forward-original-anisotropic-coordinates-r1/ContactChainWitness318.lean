module
public import ContactWeightWitness318
public section
noncomputable section
namespace ContactChainWitness318
open CircuitReplay Raw318FinalReplay
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Literal forward evaluation of the 30 quadratic detector-chain gates.
Every coordinate is computed in original row order; no algebraic solution
or unspecified gate value is an input. -/
@[expose] def value159 (w : Assignment) : ℚ := -((-1) + (-1 * w 126 * w 156))

@[expose] def value160 (w : Assignment) : ℚ := -((-1 * w 125 * w 151) + (-1 * (value159 w) * (value159 w)))

@[expose] def value161 (w : Assignment) : ℚ := -((-1 * w 58 * w 151) + (-1 * (value160 w) * (value160 w)))

@[expose] def value162 (w : Assignment) : ℚ := -((-2 * w 59 * w 151))

@[expose] def value163 (w : Assignment) : ℚ := -((-1 * w 60 * w 151) + (-1 * (value161 w) * (value161 w)) + (-2 * (value162 w) * (value162 w)))

@[expose] def value164 (w : Assignment) : ℚ := -((-2 * w 61 * w 151) + (-2 * (value161 w) * (value162 w)))

@[expose] def value165 (w : Assignment) : ℚ := -((-2 * w 62 * w 151) + (-1 * (value163 w) * (value163 w)) + (-2 * (value164 w) * (value164 w)))

@[expose] def value166 (w : Assignment) : ℚ := -((-2 * w 63 * w 151) + (-2 * (value163 w) * (value164 w)))

@[expose] def value167 (w : Assignment) : ℚ := -((-1 * w 64 * w 151) + (-1 * (value165 w) * (value165 w)) + (-2 * (value166 w) * (value166 w)))

@[expose] def value168 (w : Assignment) : ℚ := -((-2 * w 65 * w 151) + (-2 * (value165 w) * (value166 w)))

@[expose] def value169 (w : Assignment) : ℚ := -((-1 * w 19 * w 151) + (1 * w 151) + (-1 * (value167 w) * (value167 w)) + (-2 * (value168 w) * (value168 w)))

@[expose] def value170 (w : Assignment) : ℚ := -((1 * w 20 * w 151) + (-2 * (value167 w) * (value168 w)))

@[expose] def value171 (w : Assignment) : ℚ := -((-1 * w 23 * w 151) + (1 * w 151) + (-1 * (value169 w) * (value169 w)) + (-2 * (value170 w) * (value170 w)))

@[expose] def value172 (w : Assignment) : ℚ := -((1 * w 24 * w 151) + (-2 * (value169 w) * (value170 w)))

@[expose] def value173 (w : Assignment) : ℚ := -((-1 * w 27 * w 151) + (1 * w 151) + (-1 * (value171 w) * (value171 w)) + (-2 * (value172 w) * (value172 w)))

@[expose] def value174 (w : Assignment) : ℚ := -((1 * w 28 * w 151) + (-2 * (value171 w) * (value172 w)))

@[expose] def value175 (w : Assignment) : ℚ := -((-1 * w 31 * w 151) + (1 * w 151) + (-1 * (value173 w) * (value173 w)) + (-2 * (value174 w) * (value174 w)))

@[expose] def value176 (w : Assignment) : ℚ := -((1 * w 32 * w 151) + (-2 * (value173 w) * (value174 w)))

@[expose] def value177 (w : Assignment) : ℚ := -((-1 * w 127 * w 156) + (-1 * (value175 w) * (value175 w)) + (-2 * (value176 w) * (value176 w)))

@[expose] def value178 (w : Assignment) : ℚ := -((-2 * w 128 * w 156) + (-2 * (value175 w) * (value176 w)))

@[expose] def value179 (w : Assignment) : ℚ := -((-1 * w 129 * w 158) + (-1 * (value177 w) * (value177 w)) + (-2 * (value178 w) * (value178 w)))

@[expose] def value180 (w : Assignment) : ℚ := -((-2 * w 130 * w 158) + (-2 * (value177 w) * (value178 w)))

@[expose] def value181 (w : Assignment) : ℚ := -((-1 * w 131 * w 158) + (-1 * (value179 w) * (value179 w)) + (-2 * (value180 w) * (value180 w)))

@[expose] def value182 (w : Assignment) : ℚ := -((-2 * w 132 * w 158) + (-2 * (value179 w) * (value180 w)))

@[expose] def value183 (w : Assignment) : ℚ := -((-1 * w 133 * w 158) + (-1 * (value181 w) * (value181 w)) + (-2 * (value182 w) * (value182 w)))

@[expose] def value184 (w : Assignment) : ℚ := -((-2 * w 134 * w 158) + (-2 * (value181 w) * (value182 w)))

@[expose] def value185 (w : Assignment) : ℚ := -((-110885832 * w 0 * w 156) + (7446 * w 102 * w 156) + (-110885832 * w 118 * w 156) + (-221771664 * w 135 * w 156) + (-13860729 * w 156) + (-1 * (value183 w) * (value183 w)) + (-2 * (value184 w) * (value184 w)))

@[expose] def value186 (w : Assignment) : ℚ := -((7446 * w 103 * w 156) + (29784 * w 136 * w 156) + (-2 * (value183 w) * (value184 w)))

@[expose] def value187 (w : Assignment) : ℚ := -((2 * w 123 * w 158) + (-1 * w 137 * w 158) + (-1 * w 158) + (-1 * (value185 w) * (value185 w)) + (-2 * (value186 w) * (value186 w)))

@[expose] def value188 (w : Assignment) : ℚ := -((4 * w 124 * w 158) + (-4 * w 138 * w 158) + (-2 * (value185 w) * (value186 w)))

@[expose] def fill (w : Assignment) : Assignment := fun i => match i with
  | 159 => value159 w
  | 160 => value160 w
  | 161 => value161 w
  | 162 => value162 w
  | 163 => value163 w
  | 164 => value164 w
  | 165 => value165 w
  | 166 => value166 w
  | 167 => value167 w
  | 168 => value168 w
  | 169 => value169 w
  | 170 => value170 w
  | 171 => value171 w
  | 172 => value172 w
  | 173 => value173 w
  | 174 => value174 w
  | 175 => value175 w
  | 176 => value176 w
  | 177 => value177 w
  | 178 => value178 w
  | 179 => value179 w
  | 180 => value180 w
  | 181 => value181 w
  | 182 => value182 w
  | 183 => value183 w
  | 184 => value184 w
  | 185 => value185 w
  | 186 => value186 w
  | 187 => value187 w
  | 188 => value188 w
  | i => w i

lemma fill_input (w : Assignment) : fill w 0=w 0 := rfl

lemma preserves_first120 (S : ℚ) (w : Assignment)
    (hw : Constraints ((stage0 S).take 120) w) :
    Constraints ((stage0 S).take 120) (fill w) := by
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S] w at hw
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S] (fill w)
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
  simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,fill] using hw

@[expose] def rows (S : ℚ) := [r120 S, r121 S, r122 S, r123 S, r124 S, r125 S, r126 S, r127 S, r128 S, r129 S, r130 S, r131 S, r132 S, r133 S, r134 S, r135 S, r136 S, r137 S, r138 S, r139 S, r140 S, r141 S, r142 S, r143 S, r144 S, r145 S, r146 S, r147 S, r148 S, r149 S]

theorem literal_rows (S : ℚ) (w : Assignment) : Constraints (rows S) (fill w) := by
  have h120 : r120 S (fill w)=0 := by simp [r120,fill,value159] <;> ring
  have h121 : r121 S (fill w)=0 := by simp [r121,fill,value160] <;> ring
  have h122 : r122 S (fill w)=0 := by simp [r122,fill,value161] <;> ring
  have h123 : r123 S (fill w)=0 := by simp [r123,fill,value162] <;> ring
  have h124 : r124 S (fill w)=0 := by simp [r124,fill,value163] <;> ring
  have h125 : r125 S (fill w)=0 := by simp [r125,fill,value164] <;> ring
  have h126 : r126 S (fill w)=0 := by simp [r126,fill,value165] <;> ring
  have h127 : r127 S (fill w)=0 := by simp [r127,fill,value166] <;> ring
  have h128 : r128 S (fill w)=0 := by simp [r128,fill,value167] <;> ring
  have h129 : r129 S (fill w)=0 := by simp [r129,fill,value168] <;> ring
  have h130 : r130 S (fill w)=0 := by simp [r130,fill,value169] <;> ring
  have h131 : r131 S (fill w)=0 := by simp [r131,fill,value170] <;> ring
  have h132 : r132 S (fill w)=0 := by simp [r132,fill,value171] <;> ring
  have h133 : r133 S (fill w)=0 := by simp [r133,fill,value172] <;> ring
  have h134 : r134 S (fill w)=0 := by simp [r134,fill,value173] <;> ring
  have h135 : r135 S (fill w)=0 := by simp [r135,fill,value174] <;> ring
  have h136 : r136 S (fill w)=0 := by simp [r136,fill,value175] <;> ring
  have h137 : r137 S (fill w)=0 := by simp [r137,fill,value176] <;> ring
  have h138 : r138 S (fill w)=0 := by simp [r138,fill,value177] <;> ring
  have h139 : r139 S (fill w)=0 := by simp [r139,fill,value178] <;> ring
  have h140 : r140 S (fill w)=0 := by simp [r140,fill,value179] <;> ring
  have h141 : r141 S (fill w)=0 := by simp [r141,fill,value180] <;> ring
  have h142 : r142 S (fill w)=0 := by simp [r142,fill,value181] <;> ring
  have h143 : r143 S (fill w)=0 := by simp [r143,fill,value182] <;> ring
  have h144 : r144 S (fill w)=0 := by simp [r144,fill,value183] <;> ring
  have h145 : r145 S (fill w)=0 := by simp [r145,fill,value184] <;> ring
  have h146 : r146 S (fill w)=0 := by simp [r146,fill,value185] <;> ring
  have h147 : r147 S (fill w)=0 := by simp [r147,fill,value186] <;> ring
  have h148 : r148 S (fill w)=0 := by simp [r148,fill,value187] <;> ring
  have h149 : r149 S (fill w)=0 := by simp [r149,fill,value188] <;> ring
  simp [Constraints,rows,h120,h121,h122,h123,h124,h125,h126,h127,h128,h129,h130,h131,h132,h133,h134,h135,h136,h137,h138,h139,h140,h141,h142,h143,h144,h145,h146,h147,h148,h149]

theorem first150 (S : ℚ) (w : Assignment)
    (hw : Constraints ((stage0 S).take 120) w) :
    Constraints ((stage0 S).take 150) (fill w) := by
  change Constraints (((stage0 S).take 120) ++ rows S) _
  exact (constraints_append _ _ _).mpr ⟨preserves_first120 S w hw,literal_rows S w⟩

@[expose] def witness (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) : Assignment :=
  fill (ContactWeightWitness318.fill (DetectorGateWitness318.witness q labels h) t)

lemma witness_input (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) : witness q labels h t 0=q := by
  rw [witness,fill_input,ContactWeightWitness318.fill_input,DetectorGateWitness318.witness_input]

/-- The actual contact-parameter family covers all first150 literal rows. -/
theorem witness_first150 (S q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ)
    (hzero : h≠0) (hone : h≠1) (ht : t≠0) (hF : ContactWeightWitness318.contact t≠0)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    Constraints ((stage0 S).take 150) (witness q labels h t) :=
  first150 S _ (ContactWeightWitness318.first120 S _ t ht hF
    (DetectorGateWitness318.witness_first107 S q labels h hzero hone hg))

end ContactChainWitness318
