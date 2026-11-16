module
public import ActualConjugateCounts318
public section
noncomputable section
namespace ActualCMOrientation318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedReductionOrder318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hp : Values C u w)

/-- The remaining Frobenius/count theorem now needs only the unordered
count of ONE actual embedding. Opposite trace and orientation are produced. -/
@[expose] def OneCount (r : Roots C u w hp) (a b : Fin 3 × Fin 5 → ℤ) : Prop :=
  ∀ i : Fin 3 × Fin 5,
    counts C u w hp r false i=GaussianNeighborNorms318.minus (a i) (b i) ∨
    counts C u w hp r false i=GaussianNeighborNorms318.plus (a i) (b i)

lemma oriented_counts (r : Roots C u w hp) (s : Fin 3 × Fin 5 → Bool) (i : Fin 3 × Fin 5) :
    counts C u w hp (SelectedRayEmbeddings318.oriented C u w hp r s) false i=
      (if s i then counts C u w hp r true i else counts C u w hp r false i) ∧
    counts C u w hp (SelectedRayEmbeddings318.oriented C u w hp r s) true i=
      (if s i then counts C u w hp r false i else counts C u w hp r true i) := by
  cases hs : s i <;> simp [counts,SelectedRayEmbeddings318.oriented,hs]

/-- The actual mod7 ray gives opposite traces. A pointwise Boolean choice
then labels all15 original reductions by the exact neighboring norms. -/
theorem choose_orientation (r : Roots C u w hp) (a b : Fin 3 × Fin 5 → ℤ)
    (hray : ∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (ha7 : ∀ i, a i%7=1) (hb7 : ∀ i, b i%7=3)
    (hcount : OneCount C u w hp r a b) :
    ∃ s : Fin 3 × Fin 5 → Bool,
      GaussianSelectedOrders318.CMMatch C u w hp (SelectedRayEmbeddings318.oriented C u w hp r s) a b := by
  have hsum := ActualConjugateCounts318.all_counts_sum C u w hp r a b hray ha7 hb7
  have hchoice : ∀ i : Fin 3 × Fin 5, ∃ e : Bool,
      (if e then counts C u w hp r true i else counts C u w hp r false i)=GaussianNeighborNorms318.minus (a i) (b i) ∧
      (if e then counts C u w hp r false i else counts C u w hp r true i)=GaussianNeighborNorms318.plus (a i) (b i) := by
    intro i
    have hh := hsum i
    rcases hcount i with he|he
    · refine ⟨false,?_,?_⟩
      · exact he
      · change counts C u w hp r true i=GaussianNeighborNorms318.plus (a i) (b i)
        omega
    · refine ⟨true,?_,?_⟩
      · change counts C u w hp r true i=GaussianNeighborNorms318.minus (a i) (b i)
        omega
      · exact he
  choose s hminus hplus using hchoice
  refine ⟨s,?_⟩
  intro i
  have he := oriented_counts C u w hp r s i
  exact ⟨he.1.trans (hminus i),he.2.trans (hplus i)⟩

end ActualCMOrientation318
