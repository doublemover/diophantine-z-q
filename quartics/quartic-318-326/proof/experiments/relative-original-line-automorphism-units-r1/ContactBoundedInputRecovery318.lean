module
public import ContactBoundedInputLocalRecovery318
public section
noncomputable section
namespace ContactBoundedInputRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedSchemeHilbertData318.Data c N b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "U" => ContactBoundedRankCover318.cover c N b D
local notation "f" => ContactBoundedInputLocalRecovery318.point c N b D
local notation "q" => D.ideal.subschemeι
local notation "r" => ContactBoundedPointFamily318.into c N b f
@[expose] def models : SchemeClosedFamilyCoverModels318.Data (pullback.snd p b) q r U where
  family d := (ContactBoundedRankData318.data c N b D d).ideal.subscheme
  projection d := ContactBoundedHilbertBaseChange318.projection c N b (ContactBoundedRankData318.base c N b D d) (U.f d) rfl D
  left d := ContactBoundedHilbertBaseChange318.toFamily c N b (ContactBoundedRankData318.base c N b D d) (U.f d) rfl D
  right := ContactBoundedInputLocalRecovery318.map c N b D
  left_cartesian d := ContactBoundedHilbertBaseChange318.cartesian c N b (ContactBoundedRankData318.base c N b D d) (U.f d) rfl D
  right_cartesian d := (ContactBoundedInputLocalRecovery318.cartesian c N b D d).paste_vert
    (RelativeSchemeCoefficient318.cartesian p b (ContactBoundedRankData318.base c N b D d) (U.f d) rfl)
  over_source d := (IdealSheafCoefficientCartesian318.cartesian D.ideal
    (ContactBoundedHilbertBaseChange318.sourceMap c b (ContactBoundedRankData318.base c N b D d) (U.f d) rfl)).w.trans
      (ContactBoundedInputLocalRecovery318.source c N b D d).symm
/-- Recover the WHOLE original bounded finite-flat family, including
variable rank over disconnected bases, as its actual universal fiber. -/
@[expose] def comparison : D.ideal.subscheme ≅ ContactBoundedPointFamily318.family c N b f :=
  SchemeClosedFamilyCoverModels318.iso (pullback.snd p b) q r U (models c N b D)
@[reassoc] lemma comparison_source : (comparison c N b D).hom ≫ r=q :=
  SchemeClosedFamilyCoverModels318.iso_into _ _ _ _ _
lemma ideal_recovery : (ContactBoundedPointFamily318.extract c N b f).ideal=D.ideal := by
  have h := Scheme.Hom.ker_comp_of_isIso (comparison c N b D).hom r
  have he := congrArg (fun k : D.ideal.subscheme ⟶ pullback p b => k.ker) (comparison_source c N b D)
  exact (h.symm.trans he).trans D.ideal.ker_subschemeι
end ContactBoundedInputRecovery318
