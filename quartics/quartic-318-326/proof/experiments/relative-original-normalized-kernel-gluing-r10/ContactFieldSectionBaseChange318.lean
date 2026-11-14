module
public import ContactFlatHZeroGeometric318
public import ContactNoetherianFiniteSections318
public section
noncomputable section
namespace ContactFieldSectionBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open scoped TensorProduct
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
  (L : Line (curve (CommRingCat.of K) c))
local notation "R" => CommRingCat.of K
local instance : Module K Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤

lemma finite : Module.Finite K Γ(L.object,⊤) := ContactNoetherianFiniteSections318.finite R c L
lemma finite_projective : Module.Finite K Γ(L.object,⊤) ∧ Module.Projective K Γ(L.object,⊤) :=
  ⟨finite K c L,inferInstance⟩

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra K S := f.toAlgebra
local instance : Module S Γ((L' R S f c L).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) _ ⊤

/-- Every coefficient algebra over the ORIGINAL field is flat. Thus all
original-line global sections commute with arbitrary coefficient change,
without H1 vanishing, reducedness or finiteness of the new algebra. -/
@[expose] def equivalence : S ⊗[K] Γ(L.object,⊤) ≃ₗ[S] Γ((L' R S f c L).object,⊤) :=
  ContactFlatHZeroBaseChange318.equivalence R S f c L

lemma pure_tensor (a : S) (s : Γ(L.object,⊤)) :
    equivalence K c L S f (a ⊗ₜ[K] s)=a •
      OriginalSectionPullbackComposition318.pull (ContactRelativeCoefficientChange318.curveMap R S f c)
        L.object s := ContactFlatHZeroGeometric318.pure_tensor R S f c L a s

/-- Global sections of a line DESCENDED FROM THE FIELD form an actual
finite free module after every coefficient extension. This does not claim
that every line over an arbitrary base has locally constant H0 rank. -/
lemma finite_free : Module.Finite S Γ((L' R S f c L).object,⊤) ∧
    Module.Free S Γ((L' R S f c L).object,⊤) := by
  letI := finite K c L
  letI : Module.Free K Γ(L.object,⊤) := inferInstance
  letI : Module.Finite S (S ⊗[K] Γ(L.object,⊤)) := inferInstance
  letI : Module.Free S (S ⊗[K] Γ(L.object,⊤)) := inferInstance
  exact ⟨Module.Finite.equiv (equivalence K c L S f),
    Module.Free.of_equiv (equivalence K c L S f)⟩
end ContactFieldSectionBaseChange318
