module
public import FaithfullyFlatFinitePresentation318
public import OriginalLineAffineModel318
public section
noncomputable section
namespace FaithfullyFlatLineModule318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [hff : Module.FaithfullyFlat R S]
  (M : ModuleCat R) (L : Line (Spec S))
  (e : S ⊗[R] M ≃ₗ[S] OriginalLineAffineModel318.sections S L)

include e hff in
/-- An actual module whose faithfully flat scalar extension is the genuine
section module of an actual line is finitely presented, flat, and rank one
at every original base prime. Surjectivity on the entire prime spectrum is
used, not a selected generic point. -/
lemma properties : Module.FinitePresentation R M ∧ Module.Flat R M ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1 := by
  obtain ⟨hfp, hflat, hr⟩ := OriginalLineAffineModel318.properties S L
  let := hfp
  let := hflat
  let : Module.FinitePresentation S (S ⊗[R] M) := Module.FinitePresentation.of_equiv e.symm
  let : Module.Flat S (S ⊗[R] M) := Module.Flat.of_linearEquiv e
  let : Module.FinitePresentation R M := FaithfullyFlatFinitePresentation318.descent R S M
  let : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  refine ⟨inferInstance, inferInstance, fun p => ?_⟩
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
  have h := Module.rankAtStalk_baseChange (R := R) (M := M) q
  rw [hq] at h
  rw [← h, Module.rankAtStalk_eq_of_equiv e]
  exact hr q
end FaithfullyFlatLineModule318
