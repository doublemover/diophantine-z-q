module
public import ChainInputInvariance318
public section
noncomputable section
namespace ThreeDetectorPrePole318
open CircuitReplay Raw318FinalReplay ScaledContactWeights318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def fill (w : Assignment) (c₁ c₂ t : ℚ) : Assignment :=
  ScaledDetectorChain318.fill 1
    (ScaledDetectorChain318.fill 0 (PoleInputWitness318.fill w t) c₁ t) c₂ t

lemma fill_input (w : Assignment) (c₁ c₂ t : ℚ) : fill w c₁ c₂ t 0=w 0 := by
  simp [fill,ScaledDetectorChain318.fill,ScaledContactWeights318.fill,PoleInputWitness318.fill_input]
lemma fill190 (w : Assignment) (c₁ c₂ t : ℚ) :
    fill w c₁ c₂ t 190=PoleInputWitness318.poleInput w t := by
  simp [fill,ScaledDetectorChain318.fill,ScaledContactWeights318.fill,PoleInputWitness318.fill]
lemma fill241 (w : Assignment) (c₁ c₂ t : ℚ) :
    fill w c₁ c₂ t 241=ScaledDetectorChain318.poleInput w c₁ t := by
  simp [fill,ScaledDetectorChain318.fill,ScaledContactWeights318.fill,
    ChainInputInvariance318.poleInput_first]
lemma fill292 (w : Assignment) (c₁ c₂ t : ℚ) :
    fill w c₁ c₂ t 292=ScaledDetectorChain318.poleInput w c₂ t := by
  change ScaledDetectorChain318.poleInput
    (ScaledDetectorChain318.fill 0 (PoleInputWitness318.fill w t) c₁ t) c₂ t=_
  rw [ChainInputInvariance318.poleInput_second,ChainInputInvariance318.poleInput_first]

@[expose] def rows0 (S : ℚ) : List Row := [r0 S,r1 S,r2 S,r3 S,r4 S,r5 S,r6 S,r7 S,r8 S,r9 S,r10 S,r11 S,r12 S,r13 S,r14 S,r15 S,r16 S,r17 S,r18 S,r19 S,r20 S,r21 S,r22 S,r23 S,r24 S,r25 S,r26 S,r27 S,r28 S,r29 S,r30 S,r31 S,r32 S,r33 S,r34 S,r35 S,r36 S,r37 S,r38 S,r39 S,r40 S,r41 S,r42 S,r43 S,r44 S,r45 S,r46 S,r47 S,r48 S,r49 S,r50 S,r51 S,r52 S,r53 S,r54 S,r55 S,r56 S,r57 S,r58 S,r59 S,r60 S,r61 S,r62 S,r63 S,r64 S,r65 S,r66 S,r67 S,r68 S,r69 S,r70 S,r71 S,r72 S,r73 S,r74 S,r75 S,r76 S,r77 S,r78 S,r79 S,r80 S,r81 S,r82 S,r83 S,r84 S,r85 S,r86 S,r87 S,r88 S,r89 S,r90 S,r91 S,r92 S,r93 S,r94 S,r95 S,r96 S,r97 S,r98 S,r99 S,r100 S,r101 S,r102 S,r103 S,r104 S,r105 S,r106 S,r107 S,r108 S,r109 S,r110 S,r111 S,r112 S,r113 S,r114 S,r115 S,r116 S,r117 S,r118 S,r119 S,r120 S,r121 S,r122 S,r123 S,r124 S,r125 S,r126 S,r127 S,r128 S,r129 S,r130 S,r131 S,r132 S,r133 S,r134 S,r135 S,r136 S,r137 S,r138 S,r139 S,r140 S,r141 S,r142 S,r143 S,r144 S,r145 S,r146 S,r147 S,r148 S,r149 S,r150 S,r151 S]

@[expose] def rows1 (S : ℚ) : List Row := [r157 S,r158 S,r159 S,r160 S,r161 S,r162 S,r163 S,r164 S,r165 S,r166 S,r167 S,r168 S,r169 S,r170 S,r171 S,r172 S,r173 S,r174 S,r175 S,r176 S,r177 S,r178 S,r179 S,r180 S,r181 S,r182 S,r183 S,r184 S,r185 S,r186 S,r187 S,r188 S,r189 S,r190 S,r191 S,r192 S,r193 S,r194 S,r195 S,r196 S,r197 S,r198 S,r199 S,r200 S,r201 S,r202 S,r203 S,r204 S]

@[expose] def rows2 (S : ℚ) : List Row := [r210 S,r211 S,r212 S,r213 S,r214 S,r215 S,r216 S,r217 S,r218 S,r219 S,r220 S,r221 S,r222 S,r223 S,r224 S,r225 S,r226 S,r227 S,r228 S,r229 S,r230 S,r231 S,r232 S,r233 S,r234 S,r235 S,r236 S,r237 S,r238 S,r239 S,r240 S,r241 S,r242 S,r243 S,r244 S,r245 S,r246 S,r247 S,r248 S,r249 S,r250 S,r251 S,r252 S,r253 S,r254 S,r255 S,r256 S,r257 S]

@[expose] def rows (S : ℚ) : List Row := rows0 S ++ rows1 S ++ rows2 S

lemma first146 (w : Assignment) (t : ℚ) : PoleInputWitness318.fill w t 146=1/t := by
  simp [PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]
lemma first143 (w : Assignment) (t : ℚ) : PoleInputWitness318.fill w t 143=w 143 := by
  simp [PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]
lemma first145 (w : Assignment) (t : ℚ) : PoleInputWitness318.fill w t 145=w 145 := by
  simp [PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

/-- One block is filled from its actual scale and actual incoming assignment.
The two rational pole witnesses are not supplied until all three b's exist. -/
theorem block1 (S : ℚ) (w : Assignment) (c t : ℚ)
    (ht : t≠0) (hc : c≠0) (hscale : c=w 143+w 145)
    (hinv : w 146=1/t) (hd : delta c t≠0) (hF : ContactWeightWitness318.contact (parameter c t)≠0)
    (hr : ScaledDetectorChain318.realChain w c t≠0) :
    Constraints (rows1 S) (ScaledDetectorChain318.fill 0 w c t) := by
  have hw := ScaledContactWeights318.rows1 S w c t ht hscale hinv hF
  have hg := ScaledDetectorChain318.chain_rows1 S w c t
  have htrace := ScaledDetectorChain318.trace_row1 S w c t hr
  have hpole := ScaledDetectorChain318.pole_row1 S w c t hc hd hF
  have hw' : Constraints [r157 S,r158 S,r159 S,r160 S,r161 S,r162 S,r163 S,r164 S,r165 S,r166 S,r167 S,r168 S,r169 S,r170 S,r171 S,r172 S]
      (ScaledDetectorChain318.fill 0 w c t) := by
    simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
    simpa [r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170,r171,r172,ScaledDetectorChain318.fill] using hw
  unfold rows1
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw' hg ⊢
  exact ⟨hw'.1,hw'.2.1,hw'.2.2.1,hw'.2.2.2.1,hw'.2.2.2.2.1,hw'.2.2.2.2.2.1,hw'.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2.1,hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,htrace,hpole⟩

theorem block2 (S : ℚ) (w : Assignment) (c t : ℚ)
    (ht : t≠0) (hc : c≠0) (hscale : c=w 145)
    (hinv : w 146=1/t) (hd : delta c t≠0) (hF : ContactWeightWitness318.contact (parameter c t)≠0)
    (hr : ScaledDetectorChain318.realChain w c t≠0) :
    Constraints (rows2 S) (ScaledDetectorChain318.fill 1 w c t) := by
  have hw := ScaledContactWeights318.rows2 S w c t ht hscale hinv hF
  have hg := ScaledDetectorChain318.chain_rows2 S w c t
  have htrace := ScaledDetectorChain318.trace_row2 S w c t hr
  have hpole := ScaledDetectorChain318.pole_row2 S w c t hc hd hF
  have hw' : Constraints [r210 S,r211 S,r212 S,r213 S,r214 S,r215 S,r216 S,r217 S,r218 S,r219 S,r220 S,r221 S,r222 S,r223 S,r224 S,r225 S]
      (ScaledDetectorChain318.fill 1 w c t) := by
    simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
    simpa [r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225,ScaledDetectorChain318.fill] using hw
  unfold rows2
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw' hg ⊢
  exact ⟨hw'.1,hw'.2.1,hw'.2.2.1,hw'.2.2.2.1,hw'.2.2.2.2.1,hw'.2.2.2.2.2.1,hw'.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hw'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2.1,hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,htrace,hpole⟩

theorem nonpole_rows (S : ℚ) (w : Assignment) (c₁ c₂ t : ℚ)
    (hw : Constraints ((stage0 S).take 152) (PoleInputWitness318.fill w t))
    (ht : t≠0) (hc₁ : c₁≠0) (hc₂ : c₂≠0)
    (hs₁ : c₁=w 143+w 145) (hs₂ : c₂=w 145)
    (hd₁ : delta c₁ t≠0) (hd₂ : delta c₂ t≠0)
    (hF₁ : ContactWeightWitness318.contact (parameter c₁ t)≠0)
    (hF₂ : ContactWeightWitness318.contact (parameter c₂ t)≠0)
    (hr₁ : ScaledDetectorChain318.realChain w c₁ t≠0)
    (hr₂ : ScaledDetectorChain318.realChain w c₂ t≠0) :
    Constraints (rows S) (fill w c₁ c₂ t) := by
  have h1 := block1 S (PoleInputWitness318.fill w t) c₁ t ht hc₁
    (by simpa only [first143,first145] using hs₁) (first146 w t) hd₁ hF₁
    (by simpa only [ChainInputInvariance318.realChain_first] using hr₁)
  have h2 := block2 S (ScaledDetectorChain318.fill 0 (PoleInputWitness318.fill w t) c₁ t)
    c₂ t ht hc₂ (by simpa [ScaledDetectorChain318.fill,ScaledContactWeights318.fill,first145] using hs₂)
    (by simp [ScaledDetectorChain318.fill,ScaledContactWeights318.fill,first146]) hd₂ hF₂
    (by simpa only [ChainInputInvariance318.realChain_second,ChainInputInvariance318.realChain_first] using hr₂)
  have h0' : Constraints (rows0 S) (fill w c₁ c₂ t) := by
    change Constraints [r0 S,r1 S,r2 S,r3 S,r4 S,r5 S,r6 S,r7 S,r8 S,r9 S,r10 S,r11 S,r12 S,r13 S,r14 S,r15 S,r16 S,r17 S,r18 S,r19 S,r20 S,r21 S,r22 S,r23 S,r24 S,r25 S,r26 S,r27 S,r28 S,r29 S,r30 S,r31 S,r32 S,r33 S,r34 S,r35 S,r36 S,r37 S,r38 S,r39 S,r40 S,r41 S,r42 S,r43 S,r44 S,r45 S,r46 S,r47 S,r48 S,r49 S,r50 S,r51 S,r52 S,r53 S,r54 S,r55 S,r56 S,r57 S,r58 S,r59 S,r60 S,r61 S,r62 S,r63 S,r64 S,r65 S,r66 S,r67 S,r68 S,r69 S,r70 S,r71 S,r72 S,r73 S,r74 S,r75 S,r76 S,r77 S,r78 S,r79 S,r80 S,r81 S,r82 S,r83 S,r84 S,r85 S,r86 S,r87 S,r88 S,r89 S,r90 S,r91 S,r92 S,r93 S,r94 S,r95 S,r96 S,r97 S,r98 S,r99 S,r100 S,r101 S,r102 S,r103 S,r104 S,r105 S,r106 S,r107 S,r108 S,r109 S,r110 S,r111 S,r112 S,r113 S,r114 S,r115 S,r116 S,r117 S,r118 S,r119 S,r120 S,r121 S,r122 S,r123 S,r124 S,r125 S,r126 S,r127 S,r128 S,r129 S,r130 S,r131 S,r132 S,r133 S,r134 S,r135 S,r136 S,r137 S,r138 S,r139 S,r140 S,r141 S,r142 S,r143 S,r144 S,r145 S,r146 S,r147 S,r148 S,r149 S,r150 S,r151 S] _ at hw
    unfold rows0
    simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
    simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148,r149,r150,r151,fill,ScaledDetectorChain318.fill,ScaledContactWeights318.fill] using hw
  have h1' : Constraints (rows1 S) (fill w c₁ c₂ t) := by
    unfold rows1 at h1 ⊢
    simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at h1 ⊢
    simpa [r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204,fill,ScaledDetectorChain318.fill,ScaledContactWeights318.fill] using h1
  exact (constraints_append _ _ _).mpr ⟨(constraints_append _ _ _).mpr ⟨h0',h1'⟩,h2⟩

end ThreeDetectorPrePole318
