module
public import ComplementRootAction318
public import SourceTwistFieldEquiv318
public section
noncomputable section
open scoped BigOperators
namespace LabeledContactFieldReconstruction318
open ComplementSquareclass318 SourceTwistArithmetic318 KummerTensorField318
variable {L : Type*} [Field L] [Algebra (RatFunc ℚ) L] [FiniteDimensional (RatFunc ℚ) L]
variable (c : Fin 4 → ℚˣ)

lemma parameter_ne_zero (i : Fin 4) : SourceKummerField318.parameter c i ≠ 0 := by
  intro h
  have hn := SourceKummerField318.product_nonsquare c {i} (by simp)
  apply hn
  simpa only [Finset.prod_singleton, h] using (IsSquare.zero : IsSquare (0 : RatFunc ℚ))

/-- Actual complementary radicals of the original four labeled contact
functions suffice. No assertion of PEL existence is encoded in this structure. -/
structure RadicalData where
  root : Fin 4 → L
  square : ∀ i, root i ^ 2 = algebraMap (RatFunc ℚ) L
    (complementaryProduct (SourceKummerField318.parameter c) i)
  degree : Module.finrank (RatFunc ℚ) L = 16

variable (d : RadicalData (L := L) c)

/-- The map is explicitly the recovered-root evaluation into the ORIGINAL
candidate field, rather than a new field selected from its numerical degree. -/
@[expose] def equivalence : Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L :=
  ComplementRootReconstruction318.equivalence _ (parameter_ne_zero c) d.root d.square d.degree

@[simp] theorem equivalence_generator (i : Fin 4) :
    equivalence c d (FourRootAutomorphisms318.generator (SourceKummerField318.parameter c) i) =
      complementaryProduct d.root i /
        algebraMap (RatFunc ℚ) L (allProduct (SourceKummerField318.parameter c)) :=
  ComplementRootReconstruction318.equivalence_generator _ _ _ _ _ i

include d in
/-- Arbitrary rational twists remain until actual rational coefficient
scalings of ALL four original quotient Jacobians determine them. Equal j alone
is not the input of this theorem. -/
theorem fixed_model_of_published_scalings
    (h : ∀ i, ∃ u : ℚ, u ≠ 0 ∧
      complementaryProduct (fun j => (c j : ℚ)) i ^ 2 * cubicA i = u ^ 4 * publishedA i ∧
      complementaryProduct (fun j => (c j : ℚ)) i ^ 3 * cubicB i = u ^ 6 * publishedB i) :
    Nonempty (Raw (SourceKummerField318.parameter units) ≃ₐ[RatFunc ℚ] L) := by
  obtain ⟨e⟩ := SourceTwistFieldEquiv318.source_equiv_of_published_scalings c h
  exact ⟨e.symm.trans (equivalence c d)⟩

/-- The field comparison retains the supplied labeled action on every element. -/
theorem equivariant (s : Fin 4 → Bool) (e : L ≃ₐ[RatFunc ℚ] L)
    (he : ∀ i, e (d.root i) = algebraMap (RatFunc ℚ) L
      (complementaryProduct (ComplementRootAction318.sign s) i) * d.root i)
    (w : Raw (SourceKummerField318.parameter c)) :
    e (equivalence c d w) = equivalence c d
      (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) s w) :=
  ComplementRootAction318.evaluation_equivariant _ (parameter_ne_zero c) d.root d.square s e he w
end LabeledContactFieldReconstruction318
