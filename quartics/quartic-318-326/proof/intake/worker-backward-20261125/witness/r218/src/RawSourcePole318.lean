module
public import Raw318FinalReplayData
public import SourcePole318
public section
namespace RawSourcePole318
open CircuitReplay Raw318FinalReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! These theorems consume the literal 288-equation source, not a semantic
replacement predicate. The affine CSE values H=17e-w and T=-3t are respected.
Generated from the pinned raw IR; every claimed equality is kernel checked. -/
theorem detector0_no_negative_odd
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hb : v (w 190)=k) (hk : Odd k)
    (h17 : v (17:ℚ)=0) (h3 : v (3:ℚ)=0) : 0≤k := by
  have h152 : r152 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=152) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h153 : r153 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=153) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h155 : r155 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=155) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h154 : r154 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=154) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h156 : r156 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=156) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  apply SourcePole318.source_no_negative_odd v (w 190) (w 39) (w 41) (w 40) (w 42)
    (17*w 39-w 191) (w 192) (-3*w 193) k hb hk h17 h3
  · dsimp only [r152] at h152
    linear_combination -1*h152
  · dsimp only [r153] at h153
    linear_combination 1*h153
  · dsimp only [r155] at h155
    linear_combination -3*h155
  · dsimp only [r154] at h154
    linear_combination 1*h154
  · dsimp only [r156] at h156
    linear_combination 1*h156

theorem detector1_no_negative_odd
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hb : v (w 241)=k) (hk : Odd k)
    (h17 : v (17:ℚ)=0) (h3 : v (3:ℚ)=0) : 0≤k := by
  have h205 : r205 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=205) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h206 : r206 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=206) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h208 : r208 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=208) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h207 : r207 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=207) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h209 : r209 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=209) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  apply SourcePole318.source_no_negative_odd v (w 241) (w 43) (w 45) (w 44) (w 46)
    (17*w 43-w 242) (w 243) (-3*w 244) k hb hk h17 h3
  · dsimp only [r205] at h205
    linear_combination -1*h205
  · dsimp only [r206] at h206
    linear_combination 1*h206
  · dsimp only [r208] at h208
    linear_combination -3*h208
  · dsimp only [r207] at h207
    linear_combination 1*h207
  · dsimp only [r209] at h209
    linear_combination 1*h209

theorem detector2_no_negative_odd
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hb : v (w 292)=k) (hk : Odd k)
    (h17 : v (17:ℚ)=0) (h3 : v (3:ℚ)=0) : 0≤k := by
  have h258 : r258 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=258) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h259 : r259 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=259) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h261 : r261 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=261) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h260 : r260 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=260) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h262 : r262 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=262) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  apply SourcePole318.source_no_negative_odd v (w 292) (w 47) (w 49) (w 48) (w 50)
    (17*w 47-w 293) (w 294) (-3*w 295) k hb hk h17 h3
  · dsimp only [r258] at h258
    linear_combination -1*h258
  · dsimp only [r259] at h259
    linear_combination 1*h259
  · dsimp only [r261] at h261
    linear_combination -3*h261
  · dsimp only [r260] at h260
    linear_combination 1*h260
  · dsimp only [r262] at h262
    linear_combination 1*h262

theorem scalar_no_negative_odd
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hb : v (w 314)=k) (hk : Odd k)
    (h17 : v (17:ℚ)=0) (h3 : v (3:ℚ)=0) : 0≤k := by
  have h282 : r282 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=282) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h283 : r283 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=283) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h284 : r284 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=284) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h285 : r285 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=285) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h286 : r286 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=286) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  apply SourcePole318.source_no_negative_odd v (w 314) (w 51) (w 53) (w 52) (w 54)
    (17*w 51-w 315) (w 316) (-3*w 317) k hb hk h17 h3
  · dsimp only [r282] at h282
    linear_combination -1*h282
  · dsimp only [r283] at h283
    linear_combination 1*h283
  · dsimp only [r284] at h284
    linear_combination -3*h284
  · dsimp only [r285] at h285
    linear_combination 1*h285
  · dsimp only [r286] at h286
    linear_combination 1*h286

end RawSourcePole318
