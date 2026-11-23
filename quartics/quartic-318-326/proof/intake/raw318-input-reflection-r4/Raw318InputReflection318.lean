module

public import Raw318FinalReplayData

public section

namespace Raw318InputReflection318

open CircuitReplay Raw318FinalReplay

/-- Transform the original assignment, including the auxiliary x² slot. -/
@[expose] def reflect (w : Assignment) : Assignment :=
  fun i => if i = 0 then -1 - w 0
    else if i = 118 then w 118 + 2 * w 0 + 1
    else w i

theorem reflect_zero (w : Assignment) : reflect w 0 = -1 - w 0 := rfl

theorem reflect_118 (w : Assignment) : reflect w 118 = w 118 + 2 * w 0 + 1 := rfl

theorem reflect_involutive : Function.Involutive reflect := by
  intro w
  funext i
  by_cases h0 : i = 0
  · subst i
    rw [reflect_zero, reflect_zero]
    ring
  · by_cases h118 : i = 118
    · subst i
      rw [reflect_118, reflect_118, reflect_zero]
      ring
    · simp only [reflect, h0, h118, ite_false]

private theorem r79_reflect (S : ℚ) (w : Assignment) :
    r79 S (reflect w) = r79 S w := by
  simp only [r79, reflect_zero, reflect_118]
  ring

private theorem r96_reflect (S : ℚ) (w : Assignment) :
    r96 S (reflect w) = r96 S w := by
  simp only [r96, reflect_zero, reflect_118,
    show reflect w 102 = w 102 from rfl,
    show reflect w 103 = w 103 from rfl,
    show reflect w 135 = w 135 from rfl]
  ring

private theorem r97_reflect (S : ℚ) (w : Assignment) :
    r97 S (reflect w) = r97 S w := by
  simp only [r97, reflect_zero, reflect_118,
    show reflect w 103 = w 103 from rfl,
    show reflect w 102 = w 102 from rfl,
    show reflect w 136 = w 136 from rfl]
  ring

private theorem r146_reflect (S : ℚ) (w : Assignment) :
    r146 S (reflect w) = r146 S w := by
  simp only [r146, reflect_zero, reflect_118,
    show reflect w 156 = w 156 from rfl,
    show reflect w 102 = w 102 from rfl,
    show reflect w 135 = w 135 from rfl,
    show reflect w 183 = w 183 from rfl,
    show reflect w 184 = w 184 from rfl,
    show reflect w 185 = w 185 from rfl]
  ring

private theorem r199_reflect (S : ℚ) (w : Assignment) :
    r199 S (reflect w) = r199 S w := by
  simp only [r199, reflect_zero, reflect_118,
    show reflect w 207 = w 207 from rfl,
    show reflect w 102 = w 102 from rfl,
    show reflect w 135 = w 135 from rfl,
    show reflect w 234 = w 234 from rfl,
    show reflect w 235 = w 235 from rfl,
    show reflect w 236 = w 236 from rfl]
  ring

private theorem r252_reflect (S : ℚ) (w : Assignment) :
    r252 S (reflect w) = r252 S w := by
  simp only [r252, reflect_zero, reflect_118,
    show reflect w 258 = w 258 from rfl,
    show reflect w 102 = w 102 from rfl,
    show reflect w 135 = w 135 from rfl,
    show reflect w 285 = w 285 from rfl,
    show reflect w 286 = w 286 from rfl,
    show reflect w 287 = w 287 from rfl]
  ring

private theorem r263_reflect (S : ℚ) (w : Assignment) :
    r263 S (reflect w) = r263 S w := by
  simp only [r263, reflect_zero, reflect_118,
    show reflect w 296 = w 296 from rfl]
  ring

private theorem r264_reflect (S : ℚ) (w : Assignment) :
    r264 S (reflect w) = r264 S w := by
  simp only [r264, reflect_zero, reflect_118,
    show reflect w 296 = w 296 from rfl,
    show reflect w 297 = w 297 from rfl]
  ring

private theorem r265_reflect (S : ℚ) (w : Assignment) :
    r265 S (reflect w) = r265 S w := by
  simp only [r265, reflect_zero, reflect_118,
    show reflect w 298 = w 298 from rfl,
    show reflect w 296 = w 296 from rfl,
    show reflect w 297 = w 297 from rfl]
  ring

private theorem r276_reflect (S : ℚ) (w : Assignment) :
    r276 S (reflect w) = r276 S w := by
  simp only [r276, reflect_zero, reflect_118,
    show reflect w 309 = w 309 from rfl,
    show reflect w 37 = w 37 from rfl,
    show reflect w 296 = w 296 from rfl,
    show reflect w 297 = w 297 from rfl]
  ring

private theorem r280_reflect (S : ℚ) (w : Assignment) :
    r280 S (reflect w) = r280 S w := by
  simp only [r280, reflect_zero, reflect_118,
    show reflect w 312 = w 312 from rfl,
    show reflect w 313 = w 313 from rfl,
    show reflect w 296 = w 296 from rfl,
    show reflect w 297 = w 297 from rfl,
    show reflect w 311 = w 311 from rfl]
  ring

-- Each block uses the original row functions. The block size keeps the
-- definitional checks bounded; the final list equality checks coverage.
private def rowBlock0 (S : ℚ) : List Row :=
  [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S,
   r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S,
   r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S]

private theorem rowBlock0_map (S : ℚ) :
    (rowBlock0 S).map (fun r => r ∘ reflect) = rowBlock0 S := by
  rfl

private def rowBlock1 (S : ℚ) : List Row :=
  [r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S,
   r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S,
   r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S]

private theorem rowBlock1_map (S : ℚ) :
    (rowBlock1 S).map (fun r => r ∘ reflect) = rowBlock1 S := by
  rfl

private def rowBlock2 (S : ℚ) : List Row :=
  [r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S,
   r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S,
   r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S]

private theorem rowBlock2_map (S : ℚ) :
    (rowBlock2 S).map (fun r => r ∘ reflect) = rowBlock2 S := by
  rfl

private def rowBlock3 (S : ℚ) : List Row :=
  [r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S,
   r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S,
   r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S]

private theorem rowBlock3_map (S : ℚ) :
    (rowBlock3 S).map (fun r => r ∘ reflect) = rowBlock3 S := by
  calc
    (rowBlock3 S).map (fun r => r ∘ reflect) =
      [r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S ∘ reflect,
       r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S,
       r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S] := rfl
    _ = rowBlock3 S := by
      rw [rowBlock3, show r79 S ∘ reflect = r79 S from funext (r79_reflect S)]

private def rowBlock4 (S : ℚ) : List Row :=
  [r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S,
   r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S,
   r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S]

private theorem rowBlock4_map (S : ℚ) :
    (rowBlock4 S).map (fun r => r ∘ reflect) = rowBlock4 S := by
  calc
    (rowBlock4 S).map (fun r => r ∘ reflect) =
      [r96 S ∘ reflect, r97 S ∘ reflect, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S,
       r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S,
       r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S] := rfl
    _ = rowBlock4 S := by
      rw [rowBlock4, show r96 S ∘ reflect = r96 S from funext (r96_reflect S),
        show r97 S ∘ reflect = r97 S from funext (r97_reflect S)]

private def rowBlock5 (S : ℚ) : List Row :=
  [r120 S, r121 S, r122 S, r123 S, r124 S, r125 S, r126 S, r127 S,
   r128 S, r129 S, r130 S, r131 S, r132 S, r133 S, r134 S, r135 S,
   r136 S, r137 S, r138 S, r139 S, r140 S, r141 S, r142 S, r143 S]

private theorem rowBlock5_map (S : ℚ) :
    (rowBlock5 S).map (fun r => r ∘ reflect) = rowBlock5 S := by
  rfl

private def rowBlock6 (S : ℚ) : List Row :=
  [r144 S, r145 S, r146 S, r147 S, r148 S, r149 S, r150 S, r151 S,
   r152 S, r153 S, r154 S, r155 S, r156 S, r157 S, r158 S, r159 S,
   r160 S, r161 S, r162 S, r163 S, r164 S, r165 S, r166 S, r167 S]

private theorem rowBlock6_map (S : ℚ) :
    (rowBlock6 S).map (fun r => r ∘ reflect) = rowBlock6 S := by
  calc
    (rowBlock6 S).map (fun r => r ∘ reflect) =
      [r144 S, r145 S, r146 S ∘ reflect, r147 S, r148 S, r149 S, r150 S, r151 S,
       r152 S, r153 S, r154 S, r155 S, r156 S, r157 S, r158 S, r159 S,
       r160 S, r161 S, r162 S, r163 S, r164 S, r165 S, r166 S, r167 S] := rfl
    _ = rowBlock6 S := by
      rw [rowBlock6, show r146 S ∘ reflect = r146 S from funext (r146_reflect S)]

private def rowBlock7 (S : ℚ) : List Row :=
  [r168 S, r169 S, r170 S, r171 S, r172 S, r173 S, r174 S, r175 S,
   r176 S, r177 S, r178 S, r179 S, r180 S, r181 S, r182 S, r183 S,
   r184 S, r185 S, r186 S, r187 S, r188 S, r189 S, r190 S, r191 S]

private theorem rowBlock7_map (S : ℚ) :
    (rowBlock7 S).map (fun r => r ∘ reflect) = rowBlock7 S := by
  rfl

private def rowBlock8 (S : ℚ) : List Row :=
  [r192 S, r193 S, r194 S, r195 S, r196 S, r197 S, r198 S, r199 S,
   r200 S, r201 S, r202 S, r203 S, r204 S, r205 S, r206 S, r207 S,
   r208 S, r209 S, r210 S, r211 S, r212 S, r213 S, r214 S, r215 S]

private theorem rowBlock8_map (S : ℚ) :
    (rowBlock8 S).map (fun r => r ∘ reflect) = rowBlock8 S := by
  calc
    (rowBlock8 S).map (fun r => r ∘ reflect) =
      [r192 S, r193 S, r194 S, r195 S, r196 S, r197 S, r198 S, r199 S ∘ reflect,
       r200 S, r201 S, r202 S, r203 S, r204 S, r205 S, r206 S, r207 S,
       r208 S, r209 S, r210 S, r211 S, r212 S, r213 S, r214 S, r215 S] := rfl
    _ = rowBlock8 S := by
      rw [rowBlock8, show r199 S ∘ reflect = r199 S from funext (r199_reflect S)]

private def rowBlock9 (S : ℚ) : List Row :=
  [r216 S, r217 S, r218 S, r219 S, r220 S, r221 S, r222 S, r223 S,
   r224 S, r225 S, r226 S, r227 S, r228 S, r229 S, r230 S, r231 S,
   r232 S, r233 S, r234 S, r235 S, r236 S, r237 S, r238 S, r239 S]

private theorem rowBlock9_map (S : ℚ) :
    (rowBlock9 S).map (fun r => r ∘ reflect) = rowBlock9 S := by
  rfl

private def rowBlock10 (S : ℚ) : List Row :=
  [r240 S, r241 S, r242 S, r243 S, r244 S, r245 S, r246 S, r247 S,
   r248 S, r249 S, r250 S, r251 S, r252 S, r253 S, r254 S, r255 S,
   r256 S, r257 S, r258 S, r259 S, r260 S, r261 S, r262 S, r263 S]

private theorem rowBlock10_map (S : ℚ) :
    (rowBlock10 S).map (fun r => r ∘ reflect) = rowBlock10 S := by
  calc
    (rowBlock10 S).map (fun r => r ∘ reflect) =
      [r240 S, r241 S, r242 S, r243 S, r244 S, r245 S, r246 S, r247 S,
       r248 S, r249 S, r250 S, r251 S, r252 S ∘ reflect, r253 S, r254 S, r255 S,
       r256 S, r257 S, r258 S, r259 S, r260 S, r261 S, r262 S, r263 S ∘ reflect] := rfl
    _ = rowBlock10 S := by
      rw [rowBlock10, show r252 S ∘ reflect = r252 S from funext (r252_reflect S),
        show r263 S ∘ reflect = r263 S from funext (r263_reflect S)]

private def rowBlock11 (S : ℚ) : List Row :=
  [r264 S, r265 S, r266 S, r267 S, r268 S, r269 S, r270 S, r271 S,
   r272 S, r273 S, r274 S, r275 S, r276 S, r277 S, r278 S, r279 S,
   r280 S, r281 S, r282 S, r283 S, r284 S, r285 S, r286 S, r287 S]

private theorem rowBlock11_map (S : ℚ) :
    (rowBlock11 S).map (fun r => r ∘ reflect) = rowBlock11 S := by
  calc
    (rowBlock11 S).map (fun r => r ∘ reflect) =
      [r264 S ∘ reflect, r265 S ∘ reflect, r266 S, r267 S, r268 S, r269 S, r270 S, r271 S,
       r272 S, r273 S, r274 S, r275 S, r276 S ∘ reflect, r277 S, r278 S, r279 S,
       r280 S ∘ reflect, r281 S, r282 S, r283 S, r284 S, r285 S, r286 S, r287 S] := rfl
    _ = rowBlock11 S := by
      rw [rowBlock11, show r264 S ∘ reflect = r264 S from funext (r264_reflect S),
        show r265 S ∘ reflect = r265 S from funext (r265_reflect S),
        show r276 S ∘ reflect = r276 S from funext (r276_reflect S),
        show r280 S ∘ reflect = r280 S from funext (r280_reflect S)]

-- Only the 288-element literal-list comparison needs deeper definitional reduction.
set_option maxRecDepth 4096 in
private theorem stage0_blocks (S : ℚ) : stage0 S =
      rowBlock0 S ++ rowBlock1 S ++ rowBlock2 S ++ rowBlock3 S ++
      rowBlock4 S ++ rowBlock5 S ++ rowBlock6 S ++ rowBlock7 S ++
      rowBlock8 S ++ rowBlock9 S ++ rowBlock10 S ++ rowBlock11 S := rfl

/-- The full frozen source, not merely the affected rows, is invariant. -/
theorem stage0_map (S : ℚ) :
    (stage0 S).map (fun r => r ∘ reflect) = stage0 S := by
  rw [stage0_blocks]
  simp only [List.map_append, rowBlock0_map, rowBlock1_map, rowBlock2_map, rowBlock3_map,
    rowBlock4_map, rowBlock5_map, rowBlock6_map, rowBlock7_map,
    rowBlock8_map, rowBlock9_map, rowBlock10_map, rowBlock11_map]

theorem constraints_reflect (S : ℚ) (w : Assignment) :
    Constraints (stage0 S) (reflect w) ↔ Constraints (stage0 S) w := by
  rw [← constraints_map (stage0 S) reflect w, stage0_map S]

theorem hasSolution_reflect (S q : ℚ) (h : HasSolution (stage0 S) q) :
    HasSolution (stage0 S) (-1 - q) := by
  obtain ⟨w, hw, hrows⟩ := h
  refine ⟨reflect w, ?_, (constraints_reflect S w).mpr hrows⟩
  rw [reflect_zero, hw]

theorem hasSolution_reflect_iff (S q : ℚ) :
    HasSolution (stage0 S) (-1 - q) ↔ HasSolution (stage0 S) q := by
  constructor
  · intro h
    have h' := hasSolution_reflect S (-1 - q) h
    have heq : -1 - (-1 - q) = q := by ring
    exact heq ▸ h'
  · exact hasSolution_reflect S q

theorem zero_iff_negOne (S : ℚ) :
    HasSolution (stage0 S) 0 ↔ HasSolution (stage0 S) (-1) := by
  simpa only [sub_zero] using (hasSolution_reflect_iff S 0).symm

/-- The input reflection extends any forward theorem on the nonnegative
integers to all integers; it does not supply that theorem. -/
theorem hasSolution_at_integer_of_nonneg (S : ℚ)
    (h : ∀ a : ℤ, 0 ≤ a → HasSolution (stage0 S) (a : ℚ)) (a : ℤ) :
    HasSolution (stage0 S) (a : ℚ) := by
  by_cases ha : 0 ≤ a
  · exact h a ha
  · have hb : 0 ≤ (-1 - a : ℤ) := by omega
    have h' := hasSolution_reflect S ((-1 - a : ℤ) : ℚ) (h (-1 - a) hb)
    have heq : -1 - ((-1 - a : ℤ) : ℚ) = (a : ℚ) := by
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring
    exact heq ▸ h'

/-- The +1 in the transformed square slot is necessary, already at x=0. -/
theorem omittedUnit_breaks_r79 (S : ℚ) :
    r79 S (fun i => if i = 0 then -1 else 0) = -1 := by
  norm_num [r79]

end Raw318InputReflection318
