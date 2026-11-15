module
public import ActualOriginalFiveOrderWeightControl318
public section
noncomputable section
namespace ActualOriginalMixedTranslation318
open ActualOriginalIteratedDifference318

lemma actual_mixed_translation {E F : Type*} [AddCommMonoid E] [Sub F]
    (g : E → F) (v : E) (us : List E) : ∀ x,
    mixedDifference (fun z => g (z+v)) us x=mixedDifference g us (x+v) := by
  induction us with
  | nil => intro x; rfl
  | cons u us ih =>
    intro x
    simp only [mixedDifference,ih]
    congr 1
    congr 1
    ac_rfl

lemma actual_mixed_sub {E F : Type*} [Add E] [AddCommGroup F]
    (g g' : E → F) (us : List E) : ∀ x,
    mixedDifference (fun z => g z-g' z) us x=
      mixedDifference g us x-mixedDifference g' us x := by
  induction us with
  | nil => intro x; rfl
  | cons u us ih => intro x; simp only [mixedDifference,ih]; abel

/-- The extra step is a genuine mixed difference of the SAME function.
Commutation uses only the actual additive coordinates and finite subtraction. -/
lemma actual_mixed_step {E F : Type*} [AddCommMonoid E] [AddCommGroup F]
    (g : E → F) (v : E) (us : List E) (x : E) :
    mixedDifference (fun z => g (z+v)-g z) us x=mixedDifference g (v::us) x := by
  rw [actual_mixed_sub,actual_mixed_translation]
  rfl

end ActualOriginalMixedTranslation318
