module
public import ActualTwoDescentOriginalRootIdeals318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootTranslations318
open ActualTwoDescentOriginalRootIdeals318
variable {K : Type*} [Field K] [CharZero K]

def rootTranslateX (n x : K) : Fin 3 → K :=
  ![-3*n^2/x,n*(x+3*n)/(x-n),-3*n*(x-n)/(x+3*n)]
def rootTranslateY (n x y : K) : Fin 3 → K :=
  ![3*n^2*y/x^2,-4*n^2*y/(x-n)^2,-12*n^2*y/(x+3*n)^2]
def rootWeight (n x : K) (i : Fin 3) : K := x-root n i

def AwayRoots (n x : K) : Prop := ∀ i : Fin 3, rootWeight n x i ≠ 0

lemma actual_root_weights (n x : K) :
    rootWeight n x 0=x ∧ rootWeight n x 1=x-n ∧ rootWeight n x 2=x+3*n := by
  simp [rootWeight,root,sub_neg_eq_add]

/-- Each of the three rational maps preserves the ORIGINAL cubic. -/
theorem actual_root_translation_curve (n x y : K) (i : Fin 3)
    (hd : rootWeight n x i ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    (rootTranslateY n x y i)^2=rootTranslateX n x i*
      (rootTranslateX n x i-n)*(rootTranslateX n x i+3*n) := by
  fin_cases i <;> simp only [rootWeight,root,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,sub_zero,sub_neg_eq_add] at hd
  all_goals
    simp only [rootTranslateX,rootTranslateY,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two]
    simp only [div_pow,mul_pow]
    rw [hc]
    field_simp [hd] <;> ring

/-- Numerators of the actual translated root functions. -/
def rootWeightNumerator (n x : K) : Fin 3 → Fin 3 → K :=
  ![![-3*n^2,-n*(x+3*n),3*n*(x-n)],
    ![n*(x+3*n),4*n^2,4*n*x],
    ![-3*n*(x-n),-4*n*x,12*n^2]]

lemma actual_translated_root_weight (n x : K) (i j : Fin 3)
    (hd : rootWeight n x i ≠ 0) :
    rootWeight n (rootTranslateX n x i) j=rootWeightNumerator n x i j/rootWeight n x i := by
  fin_cases i <;> fin_cases j
  all_goals
    simp [rootWeight,root] at hd
    simp only [rootWeight,root,rootTranslateX,rootWeightNumerator,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,sub_zero,sub_neg_eq_add]
    field_simp [hd] <;> ring

lemma actual_translation_away_roots (n x : K) (hn : n ≠ 0)
    (hx : AwayRoots n x) (i : Fin 3) : AwayRoots n (rootTranslateX n x i) := by
  have h0 : x ≠ 0 := by simpa [rootWeight,root] using hx 0
  have h1 : x-n ≠ 0 := by simpa [rootWeight,root] using hx 1
  have h2 : x+3*n ≠ 0 := by simpa [rootWeight,root,sub_neg_eq_add] using hx 2
  intro j
  rw [actual_translated_root_weight n x i j (hx i)]
  apply div_ne_zero _ (hx i)
  fin_cases i <;> fin_cases j <;> simp [rootWeightNumerator,hn,h0,h1,h2]

end ActualTwoDescentOriginalRootTranslations318
