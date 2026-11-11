module
public import ActualPadeRatios318
public section
noncomputable section
namespace DetectorGateWitness318
open CircuitReplay Raw318FinalReplay
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Literal forward evaluation of the 28 quadratic detector/product gates.
Every coordinate is computed in original row order; no algebraic solution
or unspecified gate value is an input. -/
@[expose] def value118 (w : Assignment) : ℚ := -((-1 * w 0 * w 0))

@[expose] def value119 (w : Assignment) : ℚ := -((-1 * w 106 * w 114) + (-2 * w 107 * w 115))

@[expose] def value120 (w : Assignment) : ℚ := -((-1 * w 106 * w 115) + (-1 * w 107 * w 114))

@[expose] def value121 (w : Assignment) : ℚ := -((-1 * w 106 * w 110) + (-2 * w 107 * w 111))

@[expose] def value122 (w : Assignment) : ℚ := -((-1 * w 106 * w 111) + (-1 * w 107 * w 110))

@[expose] def value123 (w : Assignment) : ℚ := -((-1 * w 110 * w 110) + (-2 * w 111 * w 111) + (-4 * w 114 * w 114) + (4 * w 114 * (value119 w)) + (-2 * w 114 * (value121 w)) + (-8 * w 115 * w 115) + (8 * w 115 * (value120 w)) + (-4 * w 115 * (value122 w)) + (-1 * (value119 w) * (value119 w)) + (1 * (value119 w) * (value121 w)) + (-2 * (value120 w) * (value120 w)) + (2 * (value120 w) * (value122 w)))

@[expose] def value124 (w : Assignment) : ℚ := -((-1 * w 110 * w 111) + (-4 * w 114 * w 115) + (2 * w 114 * (value120 w)) + (-1 * w 114 * (value122 w)) + (2 * w 115 * (value119 w)) + (-1 * w 115 * (value121 w)) + (-1 * (value119 w) * (value120 w)) + ((1 / 2) * (value119 w) * (value122 w)) + ((1 / 2) * (value120 w) * (value121 w)))

@[expose] def value125 (w : Assignment) : ℚ := -((-1 * w 90 * w 90) + (8 * w 91 * w 91))

@[expose] def value126 (w : Assignment) : ℚ := -((-1 * w 37 * w 37))

@[expose] def value127 (w : Assignment) : ℚ := -((-1 * w 102 * w 102) + (2 * w 102 * w 104) + (-2 * w 103 * w 103) + (-4 * w 103 * w 105) + (-1 * w 104 * w 104) + (-2 * w 105 * w 105))

@[expose] def value128 (w : Assignment) : ℚ := -((-1 * w 102 * w 103) + (-1 * w 102 * w 105) + (1 * w 103 * w 104) + (1 * w 104 * w 105))

@[expose] def value129 (w : Assignment) : ℚ := -((-1 * w 106 * w 106) + (2 * w 106 * w 108) + (-2 * w 107 * w 107) + (-4 * w 107 * w 109) + (-1 * w 108 * w 108) + (-2 * w 109 * w 109))

@[expose] def value130 (w : Assignment) : ℚ := -((-1 * w 106 * w 107) + (-1 * w 106 * w 109) + (1 * w 107 * w 108) + (1 * w 108 * w 109))

@[expose] def value131 (w : Assignment) : ℚ := -((-1 * w 110 * w 110) + (2 * w 110 * w 112) + (-2 * w 111 * w 111) + (-4 * w 111 * w 113) + (-1 * w 112 * w 112) + (-2 * w 113 * w 113))

@[expose] def value132 (w : Assignment) : ℚ := -((-1 * w 110 * w 111) + (-1 * w 110 * w 113) + (1 * w 111 * w 112) + (1 * w 112 * w 113))

@[expose] def value133 (w : Assignment) : ℚ := -((-1 * w 114 * w 114) + (2 * w 114 * w 116) + (-2 * w 115 * w 115) + (-4 * w 115 * w 117) + (-1 * w 116 * w 116) + (-2 * w 117 * w 117))

@[expose] def value134 (w : Assignment) : ℚ := -((-1 * w 114 * w 115) + (-1 * w 114 * w 117) + (1 * w 115 * w 116) + (1 * w 116 * w 117))

@[expose] def value135 (w : Assignment) : ℚ := -((-1 * w 0 * w 0) + ((1 / 7446) * w 0 * w 102) + (-2 * w 0 * (value118 w)) + ((-1 / 221771664) * w 102 * w 102) + ((1 / 7446) * w 102 * (value118 w)) + ((-1 / 110885832) * w 103 * w 103) + (-1 * (value118 w) * (value118 w)))

@[expose] def value136 (w : Assignment) : ℚ := -((-1 * w 0 * w 103) + ((1 / 14892) * w 102 * w 103) + (-1 * w 103 * (value118 w)))

@[expose] def value137 (w : Assignment) : ℚ := -((-1 * (value123 w) * (value123 w)) + (-8 * (value124 w) * (value124 w)))

@[expose] def value138 (w : Assignment) : ℚ := -((-1 * (value123 w) * (value124 w)))

@[expose] def value139 (w : Assignment) : ℚ := -((-1 * w 79 * w 82) + (-2 * w 80 * w 83))

@[expose] def value140 (w : Assignment) : ℚ := -((-1 * w 79 * w 83) + (-1 * w 80 * w 82))

@[expose] def value141 (w : Assignment) : ℚ := -((-1 * w 85 * (value139 w)) + (-2 * w 86 * (value140 w)))

@[expose] def value142 (w : Assignment) : ℚ := -((-1 * w 85 * (value140 w)) + (-1 * w 86 * (value139 w)))

@[expose] def value143 (w : Assignment) : ℚ := -((-1 * w 88 * (value141 w)) + (-2 * w 89 * (value142 w)))

@[expose] def value144 (w : Assignment) : ℚ := -((-1 * w 88 * (value142 w)) + (-1 * w 89 * (value141 w)))

@[expose] def value145 (w : Assignment) : ℚ := -((-1 * (value143 w) * (value143 w)) + (2 * (value144 w) * (value144 w)))

@[expose] def fill (w : Assignment) : Assignment := fun i => match i with
  | 118 => value118 w
  | 119 => value119 w
  | 120 => value120 w
  | 121 => value121 w
  | 122 => value122 w
  | 123 => value123 w
  | 124 => value124 w
  | 125 => value125 w
  | 126 => value126 w
  | 127 => value127 w
  | 128 => value128 w
  | 129 => value129 w
  | 130 => value130 w
  | 131 => value131 w
  | 132 => value132 w
  | 133 => value133 w
  | 134 => value134 w
  | 135 => value135 w
  | 136 => value136 w
  | 137 => value137 w
  | 138 => value138 w
  | 139 => value139 w
  | 140 => value140 w
  | 141 => value141 w
  | 142 => value142 w
  | 143 => value143 w
  | 144 => value144 w
  | 145 => value145 w
  | i => w i

lemma fill_input (w : Assignment) : fill w 0=w 0 := rfl

lemma preserves_first79 (S : ℚ) (w : Assignment)
    (hw : Constraints ((stage0 S).take 79) w) :
    Constraints ((stage0 S).take 79) (fill w) := by
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S] w at hw
  change Constraints [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S] (fill w)
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at hw ⊢
  simpa [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,fill] using hw

@[expose] def rows (S : ℚ) := [r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S]

theorem literal_rows (S : ℚ) (w : Assignment) : Constraints (rows S) (fill w) := by
  have h79 : r79 S (fill w)=0 := by simp [r79,fill,value118] <;> ring
  have h80 : r80 S (fill w)=0 := by simp [r80,fill,value119] <;> ring
  have h81 : r81 S (fill w)=0 := by simp [r81,fill,value120] <;> ring
  have h82 : r82 S (fill w)=0 := by simp [r82,fill,value121] <;> ring
  have h83 : r83 S (fill w)=0 := by simp [r83,fill,value122] <;> ring
  have h84 : r84 S (fill w)=0 := by simp [r84,fill,value123] <;> ring
  have h85 : r85 S (fill w)=0 := by simp [r85,fill,value124] <;> ring
  have h86 : r86 S (fill w)=0 := by simp [r86,fill,value125] <;> ring
  have h87 : r87 S (fill w)=0 := by simp [r87,fill,value126] <;> ring
  have h88 : r88 S (fill w)=0 := by simp [r88,fill,value127] <;> ring
  have h89 : r89 S (fill w)=0 := by simp [r89,fill,value128] <;> ring
  have h90 : r90 S (fill w)=0 := by simp [r90,fill,value129] <;> ring
  have h91 : r91 S (fill w)=0 := by simp [r91,fill,value130] <;> ring
  have h92 : r92 S (fill w)=0 := by simp [r92,fill,value131] <;> ring
  have h93 : r93 S (fill w)=0 := by simp [r93,fill,value132] <;> ring
  have h94 : r94 S (fill w)=0 := by simp [r94,fill,value133] <;> ring
  have h95 : r95 S (fill w)=0 := by simp [r95,fill,value134] <;> ring
  have h96 : r96 S (fill w)=0 := by simp [r96,fill,value135] <;> ring
  have h97 : r97 S (fill w)=0 := by simp [r97,fill,value136] <;> ring
  have h98 : r98 S (fill w)=0 := by simp [r98,fill,value137] <;> ring
  have h99 : r99 S (fill w)=0 := by simp [r99,fill,value138] <;> ring
  have h100 : r100 S (fill w)=0 := by simp [r100,fill,value139] <;> ring
  have h101 : r101 S (fill w)=0 := by simp [r101,fill,value140] <;> ring
  have h102 : r102 S (fill w)=0 := by simp [r102,fill,value141] <;> ring
  have h103 : r103 S (fill w)=0 := by simp [r103,fill,value142] <;> ring
  have h104 : r104 S (fill w)=0 := by simp [r104,fill,value143] <;> ring
  have h105 : r105 S (fill w)=0 := by simp [r105,fill,value144] <;> ring
  have h106 : r106 S (fill w)=0 := by simp [r106,fill,value145] <;> ring
  simp [Constraints,rows,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92,h93,h94,h95,h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106]

theorem first107 (S : ℚ) (w : Assignment)
    (hw : Constraints ((stage0 S).take 79) w) :
    Constraints ((stage0 S).take 107) (fill w) := by
  change Constraints (((stage0 S).take 79) ++ rows S) _
  exact (constraints_append _ _ _).mpr ⟨preserves_first79 S w hw,literal_rows S w⟩

@[expose] def witness (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) : Assignment :=
  fill (ActualPadeRatios318.witness q labels h)

lemma witness_input (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) : witness q labels h 0=q := by
  rw [witness,fill_input,ActualPadeRatios318.witness_input]

/-- The original common-index witness now covers all first107 literal rows. -/
theorem witness_first107 (S q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hzero : h≠0) (hone : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    Constraints ((stage0 S).take 107) (witness q labels h) :=
  first107 S _ (ActualPadeRatios318.witness_first79 S q labels h hzero hone hg)

end DetectorGateWitness318
