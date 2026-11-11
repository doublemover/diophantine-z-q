module
public import VaryingWholeQuotientRank318
public import FiniteProjectiveDualFrame318
public section
noncomputable section
namespace VaryingProjectiveQuotientLocalBasis318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
local instance localizationAlgebra (f : S) : Algebra R (Localization.Away f) :=
  ((algebraMap S (Localization.Away f)).comp (algebraMap R S)).toAlgebra
local instance localizationTower (f : S) : IsScalarTower R S (Localization.Away f) :=
  IsScalarTower.of_algebraMap_eq' rfl
variable
  (I : Ideal (S ⊗[R] A))
  [Module.Finite S ((S ⊗[R] A) ⧸ I)] [Module.Projective S ((S ⊗[R] A) ⧸ I)]
  (h : ∀ x : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[R] A) ⧸ I) x=Fintype.card ι)
/-- A finite-projective quotient of the intended rank has an ACTUAL
principal free neighborhood at every coefficient prime. -/
lemma exists_localized_basis (x : PrimeSpectrum S) : ∃ f : S, f∉x.asIdeal ∧
    Nonempty (Module.Basis ι (Localization.Away f) (LocalizedModule.Away f ((S ⊗[R] A) ⧸ I))) := by
  let Q := (S ⊗[R] A) ⧸ I
  letI : Module.FinitePresentation S Q := Module.finitePresentation_of_projective S Q
  letI : Module.Free (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl Q) :=
    Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl Q)=
      Fintype.card ι := h x
  have hb : Nonempty (Module.Basis (Fin (Fintype.card ι)) (Localization.AtPrime x.asIdeal)
      (LocalizedModule x.asIdeal.primeCompl Q)) := by
    rw [← hr]
    exact ⟨Module.finBasis (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl Q)⟩
  let b : Module.Basis ι (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl Q) :=
    (Classical.choice hb).reindex (Fintype.equivFin ι).symm
  obtain ⟨f,hf,b',-⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q)
    (Localization.AtPrime x.asIdeal) b
  exact ⟨f,hf,⟨b'⟩⟩
/-- The neighborhood basis is transported to the literal extended full
ideal quotient, not to a replacement module or chosen presentation. -/
lemma exists_extended_basis (x : PrimeSpectrum S) : ∃ f : S, f∉x.asIdeal ∧
    Nonempty (Module.Basis ι (Localization.Away f)
      ((Localization.Away f ⊗[R] A) ⧸ VaryingWholeQuotientTensor318.ideal R A S (Localization.Away f) I)) := by
  obtain ⟨f,hf,⟨b⟩⟩ := exists_localized_basis R A ι S I h x
  refine ⟨f,hf,⟨b.map ?_⟩⟩
  exact (LocalizedModule.equivTensorProduct (Submonoid.powers f) ((S ⊗[R] A) ⧸ I)).trans
    (VaryingWholeQuotientTensor318.equivalence R A S (Localization.Away f) I).toLinearEquiv
end VaryingProjectiveQuotientLocalBasis318
