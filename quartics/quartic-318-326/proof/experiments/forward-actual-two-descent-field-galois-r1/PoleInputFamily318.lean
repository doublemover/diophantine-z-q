module
public import ContactChainLimits318
public section
noncomputable section
namespace PoleInputFamily318
open Filter CircuitReplay Raw318FinalReplay PoleInputWitness318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma preserves_first150 (S : ℚ) (w : Assignment) (t : ℚ)
    (hw : Constraints ((stage0 S).take 150)
      (ContactChainWitness318.fill (ContactWeightWitness318.fill w t))) :
    Constraints ((stage0 S).take 150) (fill w t) := by
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S, r120 S, r121 S, r122 S, r123 S, r124 S, r125 S, r126 S, r127 S, r128 S, r129 S, r130 S, r131 S, r132 S, r133 S, r134 S, r135 S, r136 S, r137 S, r138 S, r139 S, r140 S, r141 S, r142 S, r143 S, r144 S, r145 S, r146 S, r147 S, r148 S, r149 S] _ at hw
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S, r120 S, r121 S, r122 S, r123 S, r124 S, r125 S, r126 S, r127 S, r128 S, r129 S, r130 S, r131 S, r132 S, r133 S, r134 S, r135 S, r136 S, r137 S, r138 S, r139 S, r140 S, r141 S, r142 S, r143 S, r144 S, r145 S, r146 S, r147 S, r148 S, r149 S] _
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
  simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148,r149,fill] using hw

theorem first152 (S : ℚ) (w : Assignment) (t : ℚ)
    (ht : t≠1) (hF : ContactWeightWitness318.contact t≠0) (hr : realChain w t≠0)
    (hw : Constraints ((stage0 S).take 150)
      (ContactChainWitness318.fill (ContactWeightWitness318.fill w t))) :
    Constraints ((stage0 S).take 152) (fill w t) := by
  change Constraints (((stage0 S).take 150) ++ [r150 S,r151 S]) _
  apply (constraints_append _ _ _).mpr
  refine ⟨preserves_first150 S w t hw,?_⟩
  change ∀ r : Row, r∈[r150 S,r151 S] → r (fill w t)=0
  intro r hmem
  rcases List.mem_cons.mp hmem with hrow|hrow
  · subst r
    exact row150 S w t hr
  · have he : r=r151 S := by simpa only [List.mem_singleton] using hrow
    subst r
    exact row151 S w t ht hF

/-- A concrete eventual family, with every quotient domain and real pole
inequality produced. This theorem fixes the actual orbit index first; it
is not a uniform-in-h assertion and cannot reverse the prime-choice order. -/
theorem eventual_actual_family (S q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hzero : h≠0) (hone : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    ∀ᶠ t : ℚ in atTop,
      (fill (DetectorGateWitness318.witness q labels h) t) 0=q ∧
      Constraints ((stage0 S).take 152) (fill (DetectorGateWitness318.witness q labels h) t) ∧
      0<poleInput (DetectorGateWitness318.witness q labels h) t ∧
      poleInput (DetectorGateWitness318.witness q labels h) t<17 ∧
      squareFactor (DetectorGateWitness318.witness q labels h) t≠0 ∧
      poleInput (DetectorGateWitness318.witness q labels h) t=
        ContactWeightWitness318.contact t*(squareFactor (DetectorGateWitness318.witness q labels h) t)^2 := by
  filter_upwards [ContactChainLimits318.eventual_pole_domain (DetectorGateWitness318.witness q labels h)]
    with t ht
  obtain ⟨ht2,hr,hpos,hsmall⟩ := ht
  have ht0 : t≠0 := by linarith
  have ht1 : t≠1 := by linarith
  have hF := (ContactChainLimits318.contact_positive t ht2).ne'
  refine ⟨?_,?_,hpos,hsmall,squareFactor_ne _ t hr ht1,pole_squareclass _ t⟩
  · rw [fill_input,DetectorGateWitness318.witness_input]
  · exact first152 S _ t ht1 hF hr
      (ContactChainWitness318.witness_first150 S q labels h t hzero hone ht0 hF hg)

end PoleInputFamily318
