module

public import Raw318FinalReplay

public import Current318FinalPolynomial

public section

namespace Current318FinalBridge

open CircuitReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedSimpArgs false

set_option linter.unnecessarySeqFocus false

set_option linter.unnecessarySimpa false

def index (j : Fin 318) : ℕ := j.val + CircuitReplay.gapOffset [] j.val

theorem index_injective : Function.Injective index := CircuitReplay.gapIndex_injective []

theorem index_zero : index 0 = 0 := by decide

theorem row0_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r290 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row0 := by
  simp only [Raw318FinalReplay.r290, Current318FinalPolynomial.row0, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row1_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r291 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row1 := by
  simp only [Raw318FinalReplay.r291, Current318FinalPolynomial.row1, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row2_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r292 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row2 := by
  simp only [Raw318FinalReplay.r292, Current318FinalPolynomial.row2, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row3_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r293 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row3 := by
  simp only [Raw318FinalReplay.r293, Current318FinalPolynomial.row3, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row4_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r294 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row4 := by
  simp only [Raw318FinalReplay.r294, Current318FinalPolynomial.row4, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row5_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r295 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row5 := by
  simp only [Raw318FinalReplay.r295, Current318FinalPolynomial.row5, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row6_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r296 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row6 := by
  simp only [Raw318FinalReplay.r296, Current318FinalPolynomial.row6, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row7_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r297 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row7 := by
  simp only [Raw318FinalReplay.r297, Current318FinalPolynomial.row7, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row8_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r298 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row8 := by
  simp only [Raw318FinalReplay.r298, Current318FinalPolynomial.row8, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row9_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r299 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row9 := by
  simp only [Raw318FinalReplay.r299, Current318FinalPolynomial.row9, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row10_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r300 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row10 := by
  simp only [Raw318FinalReplay.r300, Current318FinalPolynomial.row10, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row11_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r301 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row11 := by
  simp only [Raw318FinalReplay.r301, Current318FinalPolynomial.row11, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row12_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r302 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row12 := by
  simp only [Raw318FinalReplay.r302, Current318FinalPolynomial.row12, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row13_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r303 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row13 := by
  simp only [Raw318FinalReplay.r303, Current318FinalPolynomial.row13, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row14_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r304 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row14 := by
  simp only [Raw318FinalReplay.r304, Current318FinalPolynomial.row14, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row15_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r305 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row15 := by
  simp only [Raw318FinalReplay.r305, Current318FinalPolynomial.row15, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row16_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r306 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row16 := by
  simp only [Raw318FinalReplay.r306, Current318FinalPolynomial.row16, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row17_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r307 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row17 := by
  simp only [Raw318FinalReplay.r307, Current318FinalPolynomial.row17, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row18_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r308 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row18 := by
  simp only [Raw318FinalReplay.r308, Current318FinalPolynomial.row18, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row19_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r309 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row19 := by
  simp only [Raw318FinalReplay.r309, Current318FinalPolynomial.row19, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row20_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r310 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row20 := by
  simp only [Raw318FinalReplay.r310, Current318FinalPolynomial.row20, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row21_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r311 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row21 := by
  simp only [Raw318FinalReplay.r311, Current318FinalPolynomial.row21, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row22_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r312 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row22 := by
  simp only [Raw318FinalReplay.r312, Current318FinalPolynomial.row22, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row23_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r313 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row23 := by
  simp only [Raw318FinalReplay.r313, Current318FinalPolynomial.row23, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row24_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r314 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row24 := by
  simp only [Raw318FinalReplay.r314, Current318FinalPolynomial.row24, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row25_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r315 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row25 := by
  simp only [Raw318FinalReplay.r315, Current318FinalPolynomial.row25, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row26_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r316 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row26 := by
  simp only [Raw318FinalReplay.r316, Current318FinalPolynomial.row26, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row27_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r317 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row27 := by
  simp only [Raw318FinalReplay.r317, Current318FinalPolynomial.row27, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row28_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r318 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row28 := by
  simp only [Raw318FinalReplay.r318, Current318FinalPolynomial.row28, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row29_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r319 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row29 := by
  simp only [Raw318FinalReplay.r319, Current318FinalPolynomial.row29, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row30_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r320 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row30 := by
  simp only [Raw318FinalReplay.r320, Current318FinalPolynomial.row30, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row31_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r321 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row31 := by
  simp only [Raw318FinalReplay.r321, Current318FinalPolynomial.row31, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row32_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r322 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row32 := by
  simp only [Raw318FinalReplay.r322, Current318FinalPolynomial.row32, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row33_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r323 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row33 := by
  simp only [Raw318FinalReplay.r323, Current318FinalPolynomial.row33, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row34_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r324 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row34 := by
  simp only [Raw318FinalReplay.r324, Current318FinalPolynomial.row34, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row35_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r325 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row35 := by
  simp only [Raw318FinalReplay.r325, Current318FinalPolynomial.row35, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row36_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r326 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row36 := by
  simp only [Raw318FinalReplay.r326, Current318FinalPolynomial.row36, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row37_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r327 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row37 := by
  simp only [Raw318FinalReplay.r327, Current318FinalPolynomial.row37, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row38_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r328 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row38 := by
  simp only [Raw318FinalReplay.r328, Current318FinalPolynomial.row38, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row39_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r329 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row39 := by
  simp only [Raw318FinalReplay.r329, Current318FinalPolynomial.row39, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row40_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r330 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row40 := by
  simp only [Raw318FinalReplay.r330, Current318FinalPolynomial.row40, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row41_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r331 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row41 := by
  simp only [Raw318FinalReplay.r331, Current318FinalPolynomial.row41, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row42_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r332 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row42 := by
  simp only [Raw318FinalReplay.r332, Current318FinalPolynomial.row42, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row43_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r333 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row43 := by
  simp only [Raw318FinalReplay.r333, Current318FinalPolynomial.row43, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row44_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r334 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row44 := by
  simp only [Raw318FinalReplay.r334, Current318FinalPolynomial.row44, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row45_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r335 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row45 := by
  simp only [Raw318FinalReplay.r335, Current318FinalPolynomial.row45, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row46_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r336 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row46 := by
  simp only [Raw318FinalReplay.r336, Current318FinalPolynomial.row46, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row47_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r337 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row47 := by
  simp only [Raw318FinalReplay.r337, Current318FinalPolynomial.row47, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row48_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r338 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row48 := by
  simp only [Raw318FinalReplay.r338, Current318FinalPolynomial.row48, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row49_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r339 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row49 := by
  simp only [Raw318FinalReplay.r339, Current318FinalPolynomial.row49, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row50_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r340 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row50 := by
  simp only [Raw318FinalReplay.r340, Current318FinalPolynomial.row50, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row51_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r341 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row51 := by
  simp only [Raw318FinalReplay.r341, Current318FinalPolynomial.row51, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row52_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r342 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row52 := by
  simp only [Raw318FinalReplay.r342, Current318FinalPolynomial.row52, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row53_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r343 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row53 := by
  simp only [Raw318FinalReplay.r343, Current318FinalPolynomial.row53, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row54_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r344 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row54 := by
  simp only [Raw318FinalReplay.r344, Current318FinalPolynomial.row54, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row55_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r345 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row55 := by
  simp only [Raw318FinalReplay.r345, Current318FinalPolynomial.row55, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row56_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r346 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row56 := by
  simp only [Raw318FinalReplay.r346, Current318FinalPolynomial.row56, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row57_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r347 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row57 := by
  simp only [Raw318FinalReplay.r347, Current318FinalPolynomial.row57, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row58_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r348 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row58 := by
  simp only [Raw318FinalReplay.r348, Current318FinalPolynomial.row58, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row59_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r349 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row59 := by
  simp only [Raw318FinalReplay.r349, Current318FinalPolynomial.row59, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row60_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r350 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row60 := by
  simp only [Raw318FinalReplay.r350, Current318FinalPolynomial.row60, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row61_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r351 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row61 := by
  simp only [Raw318FinalReplay.r351, Current318FinalPolynomial.row61, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row62_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r352 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row62 := by
  simp only [Raw318FinalReplay.r352, Current318FinalPolynomial.row62, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row63_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r353 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row63 := by
  simp only [Raw318FinalReplay.r353, Current318FinalPolynomial.row63, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row64_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r354 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row64 := by
  simp only [Raw318FinalReplay.r354, Current318FinalPolynomial.row64, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row65_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r355 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row65 := by
  simp only [Raw318FinalReplay.r355, Current318FinalPolynomial.row65, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row66_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r356 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row66 := by
  simp only [Raw318FinalReplay.r356, Current318FinalPolynomial.row66, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row67_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r357 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row67 := by
  simp only [Raw318FinalReplay.r357, Current318FinalPolynomial.row67, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row68_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r358 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row68 := by
  simp only [Raw318FinalReplay.r358, Current318FinalPolynomial.row68, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row69_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r69 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row69 := by
  simp only [Raw318FinalReplay.r69, Current318FinalPolynomial.row69, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row70_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r70 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row70 := by
  simp only [Raw318FinalReplay.r70, Current318FinalPolynomial.row70, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row71_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r359 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row71 := by
  simp only [Raw318FinalReplay.r359, Current318FinalPolynomial.row71, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row72_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r360 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row72 := by
  simp only [Raw318FinalReplay.r360, Current318FinalPolynomial.row72, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row73_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r73 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row73 := by
  simp only [Raw318FinalReplay.r73, Current318FinalPolynomial.row73, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row74_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r74 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row74 := by
  simp only [Raw318FinalReplay.r74, Current318FinalPolynomial.row74, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row75_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r361 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row75 := by
  simp only [Raw318FinalReplay.r361, Current318FinalPolynomial.row75, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row76_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r362 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row76 := by
  simp only [Raw318FinalReplay.r362, Current318FinalPolynomial.row76, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row77_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r77 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row77 := by
  simp only [Raw318FinalReplay.r77, Current318FinalPolynomial.row77, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row78_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r78 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row78 := by
  simp only [Raw318FinalReplay.r78, Current318FinalPolynomial.row78, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row79_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r363 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row79 := by
  simp only [Raw318FinalReplay.r363, Current318FinalPolynomial.row79, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row80_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r364 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row80 := by
  simp only [Raw318FinalReplay.r364, Current318FinalPolynomial.row80, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row81_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r365 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row81 := by
  simp only [Raw318FinalReplay.r365, Current318FinalPolynomial.row81, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row82_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r366 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row82 := by
  simp only [Raw318FinalReplay.r366, Current318FinalPolynomial.row82, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row83_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r367 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row83 := by
  simp only [Raw318FinalReplay.r367, Current318FinalPolynomial.row83, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row84_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r368 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row84 := by
  simp only [Raw318FinalReplay.r368, Current318FinalPolynomial.row84, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row85_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r369 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row85 := by
  simp only [Raw318FinalReplay.r369, Current318FinalPolynomial.row85, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row86_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r370 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row86 := by
  simp only [Raw318FinalReplay.r370, Current318FinalPolynomial.row86, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row87_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r371 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row87 := by
  simp only [Raw318FinalReplay.r371, Current318FinalPolynomial.row87, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row88_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r372 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row88 := by
  simp only [Raw318FinalReplay.r372, Current318FinalPolynomial.row88, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row89_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r373 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row89 := by
  simp only [Raw318FinalReplay.r373, Current318FinalPolynomial.row89, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row90_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r374 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row90 := by
  simp only [Raw318FinalReplay.r374, Current318FinalPolynomial.row90, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row91_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r375 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row91 := by
  simp only [Raw318FinalReplay.r375, Current318FinalPolynomial.row91, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row92_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r376 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row92 := by
  simp only [Raw318FinalReplay.r376, Current318FinalPolynomial.row92, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row93_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r377 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row93 := by
  simp only [Raw318FinalReplay.r377, Current318FinalPolynomial.row93, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row94_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r378 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row94 := by
  simp only [Raw318FinalReplay.r378, Current318FinalPolynomial.row94, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row95_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r379 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row95 := by
  simp only [Raw318FinalReplay.r379, Current318FinalPolynomial.row95, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row96_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r380 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row96 := by
  simp only [Raw318FinalReplay.r380, Current318FinalPolynomial.row96, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row97_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r381 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row97 := by
  simp only [Raw318FinalReplay.r381, Current318FinalPolynomial.row97, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row98_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r382 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row98 := by
  simp only [Raw318FinalReplay.r382, Current318FinalPolynomial.row98, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row99_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r383 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row99 := by
  simp only [Raw318FinalReplay.r383, Current318FinalPolynomial.row99, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row100_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r384 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row100 := by
  simp only [Raw318FinalReplay.r384, Current318FinalPolynomial.row100, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row101_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r385 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row101 := by
  simp only [Raw318FinalReplay.r385, Current318FinalPolynomial.row101, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row102_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r386 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row102 := by
  simp only [Raw318FinalReplay.r386, Current318FinalPolynomial.row102, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row103_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r387 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row103 := by
  simp only [Raw318FinalReplay.r387, Current318FinalPolynomial.row103, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row104_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r388 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row104 := by
  simp only [Raw318FinalReplay.r388, Current318FinalPolynomial.row104, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row105_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r389 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row105 := by
  simp only [Raw318FinalReplay.r389, Current318FinalPolynomial.row105, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row106_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r531 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row106 := by
  simp only [Raw318FinalReplay.r531, Current318FinalPolynomial.row106, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row107_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r391 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row107 := by
  simp only [Raw318FinalReplay.r391, Current318FinalPolynomial.row107, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row108_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r392 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row108 := by
  simp only [Raw318FinalReplay.r392, Current318FinalPolynomial.row108, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row109_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r393 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row109 := by
  simp only [Raw318FinalReplay.r393, Current318FinalPolynomial.row109, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row110_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r394 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row110 := by
  simp only [Raw318FinalReplay.r394, Current318FinalPolynomial.row110, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row111_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r111 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row111 := by
  simp only [Raw318FinalReplay.r111, Current318FinalPolynomial.row111, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row112_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r395 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row112 := by
  simp only [Raw318FinalReplay.r395, Current318FinalPolynomial.row112, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row113_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r113 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row113 := by
  simp only [Raw318FinalReplay.r113, Current318FinalPolynomial.row113, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row114_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r396 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row114 := by
  simp only [Raw318FinalReplay.r396, Current318FinalPolynomial.row114, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row115_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r397 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row115 := by
  simp only [Raw318FinalReplay.r397, Current318FinalPolynomial.row115, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row116_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r116 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row116 := by
  simp only [Raw318FinalReplay.r116, Current318FinalPolynomial.row116, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row117_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r117 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row117 := by
  simp only [Raw318FinalReplay.r117, Current318FinalPolynomial.row117, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row118_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r118 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row118 := by
  simp only [Raw318FinalReplay.r118, Current318FinalPolynomial.row118, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row119_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r119 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row119 := by
  simp only [Raw318FinalReplay.r119, Current318FinalPolynomial.row119, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row120_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r398 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row120 := by
  simp only [Raw318FinalReplay.r398, Current318FinalPolynomial.row120, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row121_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r399 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row121 := by
  simp only [Raw318FinalReplay.r399, Current318FinalPolynomial.row121, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row122_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r400 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row122 := by
  simp only [Raw318FinalReplay.r400, Current318FinalPolynomial.row122, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row123_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r401 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row123 := by
  simp only [Raw318FinalReplay.r401, Current318FinalPolynomial.row123, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row124_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r402 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row124 := by
  simp only [Raw318FinalReplay.r402, Current318FinalPolynomial.row124, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row125_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r403 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row125 := by
  simp only [Raw318FinalReplay.r403, Current318FinalPolynomial.row125, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row126_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r404 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row126 := by
  simp only [Raw318FinalReplay.r404, Current318FinalPolynomial.row126, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row127_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r405 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row127 := by
  simp only [Raw318FinalReplay.r405, Current318FinalPolynomial.row127, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row128_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r406 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row128 := by
  simp only [Raw318FinalReplay.r406, Current318FinalPolynomial.row128, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row129_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r407 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row129 := by
  simp only [Raw318FinalReplay.r407, Current318FinalPolynomial.row129, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row130_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r408 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row130 := by
  simp only [Raw318FinalReplay.r408, Current318FinalPolynomial.row130, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row131_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r131 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row131 := by
  simp only [Raw318FinalReplay.r131, Current318FinalPolynomial.row131, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row132_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r409 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row132 := by
  simp only [Raw318FinalReplay.r409, Current318FinalPolynomial.row132, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row133_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r133 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row133 := by
  simp only [Raw318FinalReplay.r133, Current318FinalPolynomial.row133, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row134_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r410 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row134 := by
  simp only [Raw318FinalReplay.r410, Current318FinalPolynomial.row134, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row135_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r135 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row135 := by
  simp only [Raw318FinalReplay.r135, Current318FinalPolynomial.row135, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row136_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r411 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row136 := by
  simp only [Raw318FinalReplay.r411, Current318FinalPolynomial.row136, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row137_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r137 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row137 := by
  simp only [Raw318FinalReplay.r137, Current318FinalPolynomial.row137, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row138_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r412 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row138 := by
  simp only [Raw318FinalReplay.r412, Current318FinalPolynomial.row138, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row139_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r413 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row139 := by
  simp only [Raw318FinalReplay.r413, Current318FinalPolynomial.row139, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row140_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r414 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row140 := by
  simp only [Raw318FinalReplay.r414, Current318FinalPolynomial.row140, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row141_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r415 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row141 := by
  simp only [Raw318FinalReplay.r415, Current318FinalPolynomial.row141, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row142_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r416 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row142 := by
  simp only [Raw318FinalReplay.r416, Current318FinalPolynomial.row142, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row143_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r417 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row143 := by
  simp only [Raw318FinalReplay.r417, Current318FinalPolynomial.row143, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row144_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r418 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row144 := by
  simp only [Raw318FinalReplay.r418, Current318FinalPolynomial.row144, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row145_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r419 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row145 := by
  simp only [Raw318FinalReplay.r419, Current318FinalPolynomial.row145, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row146_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r420 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row146 := by
  simp only [Raw318FinalReplay.r420, Current318FinalPolynomial.row146, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row147_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r147 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row147 := by
  simp only [Raw318FinalReplay.r147, Current318FinalPolynomial.row147, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row148_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r148 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row148 := by
  simp only [Raw318FinalReplay.r148, Current318FinalPolynomial.row148, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row149_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r149 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row149 := by
  simp only [Raw318FinalReplay.r149, Current318FinalPolynomial.row149, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row150_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r421 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row150 := by
  simp only [Raw318FinalReplay.r421, Current318FinalPolynomial.row150, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row151_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r151 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row151 := by
  simp only [Raw318FinalReplay.r151, Current318FinalPolynomial.row151, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row152_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r422 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row152 := by
  simp only [Raw318FinalReplay.r422, Current318FinalPolynomial.row152, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row153_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r423 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row153 := by
  simp only [Raw318FinalReplay.r423, Current318FinalPolynomial.row153, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row154_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r154 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row154 := by
  simp only [Raw318FinalReplay.r154, Current318FinalPolynomial.row154, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row155_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r424 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row155 := by
  simp only [Raw318FinalReplay.r424, Current318FinalPolynomial.row155, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row156_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r156 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row156 := by
  simp only [Raw318FinalReplay.r156, Current318FinalPolynomial.row156, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row157_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r532 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row157 := by
  simp only [Raw318FinalReplay.r532, Current318FinalPolynomial.row157, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row158_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r426 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row158 := by
  simp only [Raw318FinalReplay.r426, Current318FinalPolynomial.row158, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row159_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r427 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row159 := by
  simp only [Raw318FinalReplay.r427, Current318FinalPolynomial.row159, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row160_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r428 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row160 := by
  simp only [Raw318FinalReplay.r428, Current318FinalPolynomial.row160, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row161_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r429 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row161 := by
  simp only [Raw318FinalReplay.r429, Current318FinalPolynomial.row161, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row162_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r430 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row162 := by
  simp only [Raw318FinalReplay.r430, Current318FinalPolynomial.row162, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row163_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r431 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row163 := by
  simp only [Raw318FinalReplay.r431, Current318FinalPolynomial.row163, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row164_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r432 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row164 := by
  simp only [Raw318FinalReplay.r432, Current318FinalPolynomial.row164, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row165_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r433 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row165 := by
  simp only [Raw318FinalReplay.r433, Current318FinalPolynomial.row165, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row166_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r166 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row166 := by
  simp only [Raw318FinalReplay.r166, Current318FinalPolynomial.row166, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row167_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r434 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row167 := by
  simp only [Raw318FinalReplay.r434, Current318FinalPolynomial.row167, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row168_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r435 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row168 := by
  simp only [Raw318FinalReplay.r435, Current318FinalPolynomial.row168, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row169_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r169 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row169 := by
  simp only [Raw318FinalReplay.r169, Current318FinalPolynomial.row169, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row170_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r436 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row170 := by
  simp only [Raw318FinalReplay.r436, Current318FinalPolynomial.row170, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row171_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r171 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row171 := by
  simp only [Raw318FinalReplay.r171, Current318FinalPolynomial.row171, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row172_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r172 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row172 := by
  simp only [Raw318FinalReplay.r172, Current318FinalPolynomial.row172, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row173_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r437 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row173 := by
  simp only [Raw318FinalReplay.r437, Current318FinalPolynomial.row173, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row174_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r438 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row174 := by
  simp only [Raw318FinalReplay.r438, Current318FinalPolynomial.row174, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row175_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r439 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row175 := by
  simp only [Raw318FinalReplay.r439, Current318FinalPolynomial.row175, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row176_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r440 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row176 := by
  simp only [Raw318FinalReplay.r440, Current318FinalPolynomial.row176, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row177_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r441 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row177 := by
  simp only [Raw318FinalReplay.r441, Current318FinalPolynomial.row177, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row178_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r442 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row178 := by
  simp only [Raw318FinalReplay.r442, Current318FinalPolynomial.row178, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row179_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r443 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row179 := by
  simp only [Raw318FinalReplay.r443, Current318FinalPolynomial.row179, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row180_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r444 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row180 := by
  simp only [Raw318FinalReplay.r444, Current318FinalPolynomial.row180, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row181_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r445 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row181 := by
  simp only [Raw318FinalReplay.r445, Current318FinalPolynomial.row181, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row182_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r446 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row182 := by
  simp only [Raw318FinalReplay.r446, Current318FinalPolynomial.row182, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row183_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r447 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row183 := by
  simp only [Raw318FinalReplay.r447, Current318FinalPolynomial.row183, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row184_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r184 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row184 := by
  simp only [Raw318FinalReplay.r184, Current318FinalPolynomial.row184, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row185_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r448 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row185 := by
  simp only [Raw318FinalReplay.r448, Current318FinalPolynomial.row185, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row186_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r186 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row186 := by
  simp only [Raw318FinalReplay.r186, Current318FinalPolynomial.row186, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row187_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r449 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row187 := by
  simp only [Raw318FinalReplay.r449, Current318FinalPolynomial.row187, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row188_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r188 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row188 := by
  simp only [Raw318FinalReplay.r188, Current318FinalPolynomial.row188, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row189_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r450 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row189 := by
  simp only [Raw318FinalReplay.r450, Current318FinalPolynomial.row189, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row190_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r190 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row190 := by
  simp only [Raw318FinalReplay.r190, Current318FinalPolynomial.row190, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row191_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r451 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row191 := by
  simp only [Raw318FinalReplay.r451, Current318FinalPolynomial.row191, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row192_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r452 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row192 := by
  simp only [Raw318FinalReplay.r452, Current318FinalPolynomial.row192, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row193_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r453 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row193 := by
  simp only [Raw318FinalReplay.r453, Current318FinalPolynomial.row193, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row194_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r454 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row194 := by
  simp only [Raw318FinalReplay.r454, Current318FinalPolynomial.row194, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row195_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r455 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row195 := by
  simp only [Raw318FinalReplay.r455, Current318FinalPolynomial.row195, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row196_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r456 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row196 := by
  simp only [Raw318FinalReplay.r456, Current318FinalPolynomial.row196, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row197_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r457 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row197 := by
  simp only [Raw318FinalReplay.r457, Current318FinalPolynomial.row197, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row198_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r458 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row198 := by
  simp only [Raw318FinalReplay.r458, Current318FinalPolynomial.row198, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row199_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r459 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row199 := by
  simp only [Raw318FinalReplay.r459, Current318FinalPolynomial.row199, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row200_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r200 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row200 := by
  simp only [Raw318FinalReplay.r200, Current318FinalPolynomial.row200, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row201_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r201 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row201 := by
  simp only [Raw318FinalReplay.r201, Current318FinalPolynomial.row201, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row202_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r202 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row202 := by
  simp only [Raw318FinalReplay.r202, Current318FinalPolynomial.row202, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row203_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r460 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row203 := by
  simp only [Raw318FinalReplay.r460, Current318FinalPolynomial.row203, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row204_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r461 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row204 := by
  simp only [Raw318FinalReplay.r461, Current318FinalPolynomial.row204, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row205_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r462 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row205 := by
  simp only [Raw318FinalReplay.r462, Current318FinalPolynomial.row205, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row206_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r463 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row206 := by
  simp only [Raw318FinalReplay.r463, Current318FinalPolynomial.row206, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row207_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r207 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row207 := by
  simp only [Raw318FinalReplay.r207, Current318FinalPolynomial.row207, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row208_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r464 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row208 := by
  simp only [Raw318FinalReplay.r464, Current318FinalPolynomial.row208, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row209_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r209 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row209 := by
  simp only [Raw318FinalReplay.r209, Current318FinalPolynomial.row209, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row210_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r533 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row210 := by
  simp only [Raw318FinalReplay.r533, Current318FinalPolynomial.row210, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row211_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r466 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row211 := by
  simp only [Raw318FinalReplay.r466, Current318FinalPolynomial.row211, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row212_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r467 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row212 := by
  simp only [Raw318FinalReplay.r467, Current318FinalPolynomial.row212, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row213_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r468 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row213 := by
  simp only [Raw318FinalReplay.r468, Current318FinalPolynomial.row213, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row214_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r469 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row214 := by
  simp only [Raw318FinalReplay.r469, Current318FinalPolynomial.row214, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row215_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r470 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row215 := by
  simp only [Raw318FinalReplay.r470, Current318FinalPolynomial.row215, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row216_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r471 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row216 := by
  simp only [Raw318FinalReplay.r471, Current318FinalPolynomial.row216, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row217_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r472 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row217 := by
  simp only [Raw318FinalReplay.r472, Current318FinalPolynomial.row217, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row218_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r473 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row218 := by
  simp only [Raw318FinalReplay.r473, Current318FinalPolynomial.row218, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row219_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r219 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row219 := by
  simp only [Raw318FinalReplay.r219, Current318FinalPolynomial.row219, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row220_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r474 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row220 := by
  simp only [Raw318FinalReplay.r474, Current318FinalPolynomial.row220, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row221_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r475 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row221 := by
  simp only [Raw318FinalReplay.r475, Current318FinalPolynomial.row221, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row222_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r222 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row222 := by
  simp only [Raw318FinalReplay.r222, Current318FinalPolynomial.row222, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row223_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r476 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row223 := by
  simp only [Raw318FinalReplay.r476, Current318FinalPolynomial.row223, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row224_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r224 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row224 := by
  simp only [Raw318FinalReplay.r224, Current318FinalPolynomial.row224, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row225_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r225 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row225 := by
  simp only [Raw318FinalReplay.r225, Current318FinalPolynomial.row225, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row226_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r477 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row226 := by
  simp only [Raw318FinalReplay.r477, Current318FinalPolynomial.row226, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row227_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r478 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row227 := by
  simp only [Raw318FinalReplay.r478, Current318FinalPolynomial.row227, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row228_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r479 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row228 := by
  simp only [Raw318FinalReplay.r479, Current318FinalPolynomial.row228, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row229_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r480 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row229 := by
  simp only [Raw318FinalReplay.r480, Current318FinalPolynomial.row229, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row230_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r481 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row230 := by
  simp only [Raw318FinalReplay.r481, Current318FinalPolynomial.row230, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row231_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r482 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row231 := by
  simp only [Raw318FinalReplay.r482, Current318FinalPolynomial.row231, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row232_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r483 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row232 := by
  simp only [Raw318FinalReplay.r483, Current318FinalPolynomial.row232, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row233_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r484 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row233 := by
  simp only [Raw318FinalReplay.r484, Current318FinalPolynomial.row233, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row234_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r485 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row234 := by
  simp only [Raw318FinalReplay.r485, Current318FinalPolynomial.row234, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row235_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r486 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row235 := by
  simp only [Raw318FinalReplay.r486, Current318FinalPolynomial.row235, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row236_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r487 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row236 := by
  simp only [Raw318FinalReplay.r487, Current318FinalPolynomial.row236, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row237_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r237 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row237 := by
  simp only [Raw318FinalReplay.r237, Current318FinalPolynomial.row237, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row238_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r488 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row238 := by
  simp only [Raw318FinalReplay.r488, Current318FinalPolynomial.row238, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row239_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r239 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row239 := by
  simp only [Raw318FinalReplay.r239, Current318FinalPolynomial.row239, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row240_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r489 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row240 := by
  simp only [Raw318FinalReplay.r489, Current318FinalPolynomial.row240, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row241_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r241 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row241 := by
  simp only [Raw318FinalReplay.r241, Current318FinalPolynomial.row241, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row242_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r490 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row242 := by
  simp only [Raw318FinalReplay.r490, Current318FinalPolynomial.row242, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row243_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r243 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row243 := by
  simp only [Raw318FinalReplay.r243, Current318FinalPolynomial.row243, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row244_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r491 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row244 := by
  simp only [Raw318FinalReplay.r491, Current318FinalPolynomial.row244, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row245_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r492 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row245 := by
  simp only [Raw318FinalReplay.r492, Current318FinalPolynomial.row245, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row246_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r493 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row246 := by
  simp only [Raw318FinalReplay.r493, Current318FinalPolynomial.row246, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row247_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r494 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row247 := by
  simp only [Raw318FinalReplay.r494, Current318FinalPolynomial.row247, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row248_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r495 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row248 := by
  simp only [Raw318FinalReplay.r495, Current318FinalPolynomial.row248, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row249_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r496 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row249 := by
  simp only [Raw318FinalReplay.r496, Current318FinalPolynomial.row249, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row250_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r497 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row250 := by
  simp only [Raw318FinalReplay.r497, Current318FinalPolynomial.row250, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row251_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r498 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row251 := by
  simp only [Raw318FinalReplay.r498, Current318FinalPolynomial.row251, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row252_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r499 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row252 := by
  simp only [Raw318FinalReplay.r499, Current318FinalPolynomial.row252, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row253_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r253 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row253 := by
  simp only [Raw318FinalReplay.r253, Current318FinalPolynomial.row253, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row254_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r254 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row254 := by
  simp only [Raw318FinalReplay.r254, Current318FinalPolynomial.row254, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row255_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r255 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row255 := by
  simp only [Raw318FinalReplay.r255, Current318FinalPolynomial.row255, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row256_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r500 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row256 := by
  simp only [Raw318FinalReplay.r500, Current318FinalPolynomial.row256, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row257_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r501 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row257 := by
  simp only [Raw318FinalReplay.r501, Current318FinalPolynomial.row257, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row258_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r502 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row258 := by
  simp only [Raw318FinalReplay.r502, Current318FinalPolynomial.row258, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row259_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r503 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row259 := by
  simp only [Raw318FinalReplay.r503, Current318FinalPolynomial.row259, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row260_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r260 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row260 := by
  simp only [Raw318FinalReplay.r260, Current318FinalPolynomial.row260, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row261_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r504 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row261 := by
  simp only [Raw318FinalReplay.r504, Current318FinalPolynomial.row261, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row262_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r262 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row262 := by
  simp only [Raw318FinalReplay.r262, Current318FinalPolynomial.row262, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row263_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r505 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row263 := by
  simp only [Raw318FinalReplay.r505, Current318FinalPolynomial.row263, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row264_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r506 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row264 := by
  simp only [Raw318FinalReplay.r506, Current318FinalPolynomial.row264, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row265_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r507 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row265 := by
  simp only [Raw318FinalReplay.r507, Current318FinalPolynomial.row265, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row266_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r508 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row266 := by
  simp only [Raw318FinalReplay.r508, Current318FinalPolynomial.row266, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row267_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r509 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row267 := by
  simp only [Raw318FinalReplay.r509, Current318FinalPolynomial.row267, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row268_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r510 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row268 := by
  simp only [Raw318FinalReplay.r510, Current318FinalPolynomial.row268, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row269_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r511 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row269 := by
  simp only [Raw318FinalReplay.r511, Current318FinalPolynomial.row269, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row270_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r512 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row270 := by
  simp only [Raw318FinalReplay.r512, Current318FinalPolynomial.row270, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row271_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r513 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row271 := by
  simp only [Raw318FinalReplay.r513, Current318FinalPolynomial.row271, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row272_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r514 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row272 := by
  simp only [Raw318FinalReplay.r514, Current318FinalPolynomial.row272, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row273_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r515 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row273 := by
  simp only [Raw318FinalReplay.r515, Current318FinalPolynomial.row273, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row274_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r516 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row274 := by
  simp only [Raw318FinalReplay.r516, Current318FinalPolynomial.row274, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row275_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r528 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row275 := by
  simp only [Raw318FinalReplay.r528, Current318FinalPolynomial.row275, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row276_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r276 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row276 := by
  simp only [Raw318FinalReplay.r276, Current318FinalPolynomial.row276, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row277_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r534 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row277 := by
  simp only [Raw318FinalReplay.r534, Current318FinalPolynomial.row277, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row278_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r519 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row278 := by
  simp only [Raw318FinalReplay.r519, Current318FinalPolynomial.row278, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row279_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r520 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row279 := by
  simp only [Raw318FinalReplay.r520, Current318FinalPolynomial.row279, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row280_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r521 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row280 := by
  simp only [Raw318FinalReplay.r521, Current318FinalPolynomial.row280, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row281_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r281 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row281 := by
  simp only [Raw318FinalReplay.r281, Current318FinalPolynomial.row281, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row282_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r522 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row282 := by
  simp only [Raw318FinalReplay.r522, Current318FinalPolynomial.row282, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row283_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r523 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row283 := by
  simp only [Raw318FinalReplay.r523, Current318FinalPolynomial.row283, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row284_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r524 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row284 := by
  simp only [Raw318FinalReplay.r524, Current318FinalPolynomial.row284, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row285_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r285 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row285 := by
  simp only [Raw318FinalReplay.r285, Current318FinalPolynomial.row285, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row286_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r286 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row286 := by
  simp only [Raw318FinalReplay.r286, Current318FinalPolynomial.row286, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem row287_identity (S : ℤ) (w : Assignment) :
    Raw318FinalReplay.r530 (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) Current318FinalPolynomial.row287 := by
  simp only [Raw318FinalReplay.r530, Current318FinalPolynomial.row287, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring


theorem interpreted_constraints (S : ℤ) (w : Assignment) :
    Constraints (Raw318FinalReplay.stage6 (S : ℚ)) w ↔
      SparseQuartic.Constraints S Current318FinalPolynomial.rows (fun j => w (index j)) := by
  have hrel : List.Forall₂ (fun f g : Row => ∀ w, f w = 0 ↔ g w = 0)
      (Raw318FinalReplay.stage6 (S : ℚ))
      (Current318FinalPolynomial.rows.map (fun ts => fun w =>
        SparseQuartic.residualValue S (fun j => w (index j)) ts)) := by
    simp only [Raw318FinalReplay.stage6, Current318FinalPolynomial.rows, List.map_cons, List.map_nil]
    exact List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row0_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row1_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row2_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row3_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row4_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row5_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row6_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row7_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row8_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row9_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row10_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row11_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row12_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row13_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row14_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row15_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row16_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row17_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row18_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row19_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row20_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row21_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row22_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row23_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row24_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row25_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row26_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row27_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row28_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row29_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row30_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row31_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row32_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row33_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row34_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row35_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row36_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row37_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row38_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row39_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row40_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row41_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row42_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row43_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row44_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row45_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row46_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row47_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row48_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row49_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row50_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row51_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row52_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row53_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row54_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row55_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row56_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row57_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row58_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row59_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row60_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row61_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row62_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row63_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row64_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row65_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row66_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row67_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row68_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row69_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row70_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row71_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row72_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row73_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row74_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row75_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row76_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row77_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row78_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row79_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row80_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row81_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row82_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row83_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row84_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row85_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row86_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row87_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row88_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row89_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row90_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row91_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row92_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row93_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row94_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row95_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row96_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row97_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row98_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row99_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row100_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row101_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row102_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row103_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row104_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row105_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row106_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row107_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row108_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row109_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row110_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row111_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row112_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row113_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row114_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row115_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row116_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row117_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row118_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row119_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row120_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row121_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row122_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row123_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row124_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row125_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row126_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row127_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row128_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row129_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row130_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row131_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row132_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row133_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row134_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row135_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row136_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row137_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row138_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row139_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row140_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row141_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row142_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row143_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row144_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row145_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row146_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row147_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row148_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row149_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row150_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row151_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row152_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row153_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row154_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row155_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row156_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row157_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row158_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row159_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row160_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row161_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row162_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row163_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row164_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row165_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row166_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row167_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row168_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row169_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row170_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row171_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row172_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row173_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row174_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row175_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row176_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row177_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row178_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row179_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row180_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row181_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row182_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row183_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row184_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row185_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row186_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row187_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row188_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row189_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row190_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row191_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row192_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row193_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row194_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row195_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row196_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row197_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row198_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row199_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row200_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row201_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row202_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row203_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row204_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row205_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row206_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row207_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row208_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row209_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row210_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row211_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row212_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row213_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row214_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row215_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row216_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row217_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row218_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row219_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row220_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row221_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row222_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row223_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row224_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row225_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row226_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row227_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row228_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row229_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row230_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row231_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row232_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row233_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row234_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row235_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row236_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row237_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row238_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row239_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row240_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row241_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row242_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row243_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row244_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row245_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row246_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row247_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row248_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row249_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row250_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row251_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row252_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row253_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row254_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row255_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row256_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row257_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row258_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row259_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row260_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row261_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row262_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row263_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row264_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row265_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row266_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row267_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row268_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row269_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row270_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row271_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row272_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row273_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row274_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row275_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row276_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row277_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row278_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row279_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row280_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row281_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row282_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row283_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row284_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row285_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row286_identity S w)).to_iff) (
List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row287_identity S w)).to_iff) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have h := constraints_congr _ _ hrel w
  simpa only [Constraints, SparseQuartic.Constraints, List.forall_mem_map] using h


theorem final_solution_iff (S : ℤ) (q : ℚ) :
    HasSolution (Raw318FinalReplay.stage6 (S : ℚ)) q ↔
      ∃ w : Fin 317 → ℚ, SparseQuartic.Constraints S Current318FinalPolynomial.rows (Fin.cons q w) :=
  finite_solution_iff index index_injective index_zero _ _ (interpreted_constraints S) q


theorem polynomial_zero_iff_source (q : ℚ) :
    (∃ w : Fin 317 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current318FinalPolynomial.P = 0) ↔
    HasSolution (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale : ℚ)) q := by
  exact (Current318FinalPolynomial.input_projection_iff q).trans
    ((final_solution_iff Current318FinalPolynomial.scale q).symm.trans
      (Raw318FinalReplay.source_iff_final (Current318FinalPolynomial.scale : ℚ) q).symm)


/-- The source arithmetic hypothesis is explicitly separate from the concrete,
checked compiler replay and the polynomial's SOS semantics. -/
theorem defines_integers_of_source_arithmetic
    (sourceArithmetic : ∀ q : ℚ,
      HasSolution (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale : ℚ)) q ↔
        ∃ z : ℤ, (z : ℚ) = q) :
    ∀ q : ℚ, (∃ w : Fin 317 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current318FinalPolynomial.P = 0) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  intro q
  exact (polynomial_zero_iff_source q).trans (sourceArithmetic q)


end Current318FinalBridge
