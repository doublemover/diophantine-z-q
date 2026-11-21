module
public import ActualPointedCyclicPairing318
public import ActualTZTwoBlockCoefficients318
public section
noncomputable section
namespace ActualTZFiniteBoxes318

open scoped BigOperators
open ActualPointedCyclicPairing318 ActualTZTwoBlockCoefficients318

abbrev CubeArgs (n a L : ℕ) := Fin n × ((Fin a → Fin L) × (Fin a → Fin L))
abbrev Vertex (a : ℕ) := Fin a → Bool

def shift {a L : ℕ} (axis : Fin a→ℤ)
    (v v' : Fin a→Fin L) (ω : Vertex a) : ℤ :=
  ∑ i : Fin a,if ω i then axis i*(((v i).val:ℤ)-((v' i).val:ℤ)) else 0

/-- Multiplicity is retained: each side of each difference is chosen
independently, even if the corresponding cyclic positions coincide. -/
def boxPower (n a L : ℕ) (hn : 0<n) (axis : Fin a→ℤ) (g : Fin n→ℝ) : ℝ :=
  (∑ z : CubeArgs n a L, ∏ ω : Vertex a,
    g (move hn (shift axis z.2.1 z.2.2 ω) z.1)) / ((n:ℝ)*(L:ℝ)^(2*a))

def boxNorm (n a L : ℕ) (hn : 0<n) (axis : Fin a→ℤ) (g : Fin n→ℝ) : ℝ :=
  (max 0 (boxPower n a L hn axis g)) ^ (((2^a:ℕ):ℝ)⁻¹)

theorem boxPower_neg (n a L : ℕ) (hn : 0<n) (ha : 0<a)
    (axis : Fin a→ℤ) (g : Fin n→ℝ) :
    boxPower n a L hn axis (fun x => -g x)=boxPower n a L hn axis g := by
  have hc : Fintype.card (Vertex a)=2^a := by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  have he : (-1:ℝ)^Fintype.card (Vertex a)=1 := by
    rw [hc]
    obtain ⟨a',rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    have hpow : (2^(a'+1):ℕ)=2*2^a' := by rw [pow_succ,mul_comm]
    rw [hpow,pow_mul]
    norm_num
  simp only [boxPower,Finset.prod_neg,Finset.card_univ,he,one_mul]

theorem boxNorm_neg (n a L : ℕ) (hn : 0<n) (ha : 0<a)
    (axis : Fin a→ℤ) (g : Fin n→ℝ) :
    boxNorm n a L hn axis (fun x => -g x)=boxNorm n a L hn axis g := by
  simp only [boxNorm,boxPower_neg n a L hn ha]

theorem boxNorm_le_of_abs_power (n a L : ℕ) (hn : 0<n)
    (axis : Fin a→ℤ) (g : Fin n→ℝ) {δ : ℝ} (hδ : 0≤δ)
    (hp : |boxPower n a L hn axis g|≤δ^(2^a:ℕ)) :
    boxNorm n a L hn axis g≤δ := by
  have h := max_le (pow_nonneg hδ _) ((le_abs_self _).trans hp)
  unfold boxNorm
  exact (Real.rpow_le_rpow (le_max_left _ _) h (by positivity)).trans_eq
    (Real.pow_rpow_inv_natCast hδ (by positivity : (2^a:ℕ)≠0))

/-- Label interval [-M,M] without changing difference weights. -/
def symmetric (M : ℕ) (x : Fin (2*M+1)) : ℤ := (x.val:ℤ)-(M:ℤ)

theorem symmetric_difference (M : ℕ) (x x' : Fin (2*M+1)) :
    symmetric M x-symmetric M x'=(x.val:ℤ)-(x'.val:ℤ) := by
  unfold symmetric
  ring

def coarse (h : ℕ) (m : Fin 2) : TwoBlock h :=
  ⟨m.val,by have hm := m.isLt; omega⟩

def fineCoord (h : ℕ) (i : Fin h) : TwoBlock h :=
  ⟨i.val+2,by have hi := i.isLt; omega⟩

/-- Read the actual m·h_i cross-coefficient of the chosen coarse copy. -/
def slope {h : ℕ} (Q : Quadratic (2+h)) (m : Fin 2) (t : Fin h→ℤ) : ℤ :=
  ∑ i : Fin h,qCoeff Q (coarse h m) (fineCoord h i)*t i

theorem slope_translated {h : ℕ} (Q : Quadratic (2+h)) (m : Fin 2)
    (t : Fin h→ℤ) (a wrap : ℤ) :
    slope (translated Q (bothTranslate h a) wrap) m t=slope Q m t := by
  simp only [slope,qCoeff_translated]

/-- The analytic producer selects a PET branch, but any supplied
branch must retain actual nonzero cross entries in every axis.
Bounded complexity and size are separately tested. -/
structure LocalShape where
  fineDim : ℕ
  axes : ℕ
  axes_pos : 0<axes
  table : Fin axes→Quadratic (2+fineDim)
  coarseCopy : Fin axes→Fin 2
  nonconstant : ∀ i,∃ j : Fin fineDim,
    qCoeff (table i) (coarse fineDim (coarseCopy i)) (fineCoord fineDim j)≠0

def LocalShape.coeffBound (S : LocalShape) (U : ℝ) : Prop :=
  ∀ (i : Fin S.axes) (j : Fin S.fineDim),
    |(qCoeff (S.table i) (coarse S.fineDim (S.coarseCopy i)) (fineCoord S.fineDim j):ℝ)|≤U

def localAverage (n : ℕ) (hn : 0<n) (S : LocalShape) (M : ℕ) (g : Fin n→ℝ) : ℝ :=
  (∑ h : Fin S.fineDim→Fin M,
    boxNorm n S.axes (2*M+1) hn
      (fun i => slope (S.table i) (S.coarseCopy i) (fun j => ((h j).val:ℤ)+1)) g) /
      ((M:ℝ)^S.fineDim)

theorem localAverage_neg (n : ℕ) (hn : 0<n) (S : LocalShape) (M : ℕ) (g : Fin n→ℝ) :
    localAverage n hn S M (fun x => -g x)=localAverage n hn S M g := by
  simp only [localAverage,boxNorm_neg n S.axes (2*M+1) hn S.axes_pos]

end ActualTZFiniteBoxes318
