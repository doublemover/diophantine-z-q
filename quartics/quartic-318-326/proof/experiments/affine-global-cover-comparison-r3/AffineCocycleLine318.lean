module
public import AffineOverlapCoassociativity318
public import AffineCoalgebraLine318
public section
noncomputable section
namespace AffineCocycleLine318
open CategoryTheory AlgebraicGeometry LineSheafClass318
open AffineOverlapCoaction318 AffineTripleOverlapMaps318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  (L : Line (Spec S))
  (τ : first R S (OriginalLineAffineModel318.sections S L) ⟶
    second R S (OriginalLineAffineModel318.sections S L))
  (hdiag : τ ≫ AffineOverlapDiagonal318.secondEvaluation R S (OriginalLineAffineModel318.sections S L) =
    AffineOverlapDiagonal318.firstEvaluation R S (OriginalLineAffineModel318.sections S L))
  (hτ : Cocycle R S (OriginalLineAffineModel318.sections S L) τ)

/-- Reuse the existing faithfully flat rank-one reconstruction on the actual
coalgebra just derived from the original module-overlap equations. -/
@[expose] def line : Line (Spec R) :=
  AffineCoalgebraLine318.line R S
    (AffineOverlapCoassociativity318.coalgebra R S (OriginalLineAffineModel318.sections S L) τ hdiag hτ)
    L (Iso.refl _)

/-- The reconstructed actual line pulls back to the original covering line,
using the unchanged canonical tilde/pullback reconstruction comparison. -/
@[expose] def pullbackIso :
    (LineSheafPullback318.line (Spec.map (AffineCoalgebraLine318.ringMap R S))
      (line R S L τ hdiag hτ)).object ≅ L.object :=
  AffineCoalgebraLine318.pullbackIso R S
    (AffineOverlapCoassociativity318.coalgebra R S (OriginalLineAffineModel318.sections S L) τ hdiag hτ)
    L (Iso.refl _)

/-- The descended-module comparison retains the exact original candidate
coaction, not merely an abstract scalar-extension isomorphism. -/
lemma original_coaction_compatibility :
    (ModuleCat.extendScalars (algebraMap R S)).map
      ((AffineCoalgebraModule318.adjunction (algebraMap R S)).unit.app
        (AffineCoalgebraModule318.descended (algebraMap R S) (AffineCoalgebraLine318.faithfullyFlat R S)
          (AffineOverlapCoassociativity318.coalgebra R S
            (OriginalLineAffineModel318.sections S L) τ hdiag hτ))) ≫
      (AffineCoalgebraModule318.adjunction (algebraMap R S)).toComonad.toFunctor.map
        (AffineCoalgebraModule318.moduleIso (algebraMap R S) (AffineCoalgebraLine318.faithfullyFlat R S)
          (AffineOverlapCoassociativity318.coalgebra R S
            (OriginalLineAffineModel318.sections S L) τ hdiag hτ)).hom =
    (AffineCoalgebraModule318.moduleIso (algebraMap R S) (AffineCoalgebraLine318.faithfullyFlat R S)
      (AffineOverlapCoassociativity318.coalgebra R S
        (OriginalLineAffineModel318.sections S L) τ hdiag hτ)).hom ≫
      homEquiv R S (OriginalLineAffineModel318.sections S L) τ :=
  AffineCoalgebraModule318.coaction_compatibility (algebraMap R S)
    (AffineCoalgebraLine318.faithfullyFlat R S)
    (AffineOverlapCoassociativity318.coalgebra R S (OriginalLineAffineModel318.sections S L) τ hdiag hτ)
end AffineCocycleLine318
