module
public import GlobalDescentHomEquivalence318
public section
noncomputable section
namespace OriginalBaseLineAffineUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 3000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (L : Line Y) (U : Y.affineOpens)
local instance chartAlgebra : Algebra Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) :=
  AffineFaithfullyFlatChart318.algebra f U.1
local instance chartFF : Module.FaithfullyFlat Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) :=
  AffineFaithfullyFlatChart318.module_faithfullyFlat f U.1 U.2
abbrev datum := OriginalCanonicalDescent318.datum f L
abbrev original := LineSheafPullback318.line U.2.fromSpec L
abbrev reconstructed := AffineOpenChartDescent318.line f U.1 U.2 (datum f L)
abbrev square := ActualDescentBaseChangeDiagram318.coverComparison f
  (AffineFaithfullyFlatChart318.map f U.1) (AffineFaithfullyFlatChart318.source f U.1 U.2)
  U.2.fromSpec (AffineFaithfullyFlatChart318.square f U.1 U.2)

/-- The actual affine reconstruction map followed by the canonical
original chart square compares two literal pullbacks of original lines. -/
@[expose] def coveringIso :
    (Scheme.Modules.pullback (AffineFaithfullyFlatChart318.map f U.1)).obj (reconstructed f L U).object ≅
      (Scheme.Modules.pullback (AffineFaithfullyFlatChart318.map f U.1)).obj (original L U).object :=
  AffineOpenChartDescent318.comparison f U.1 U.2 (datum f L) ≪≫ (square f U).app L.object

@[expose] def forward : ActualAffineDescentData318.Hom
    (CanonicalActualDescentFunctor318.datum Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) (reconstructed f L U))
    (CanonicalActualDescentFunctor318.datum Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) (original L U)) where
  sheafHom := (coveringIso f L U).hom
  commutes :=
    ((OriginalLocalRecoveryDescent318.affineHom f (datum f L) U).comp
      (OriginalCanonicalDescent318.baseChange f (AffineFaithfullyFlatChart318.map f U.1)
        (AffineFaithfullyFlatChart318.source f U.1 U.2) U.2.fromSpec
        (AffineFaithfullyFlatChart318.square f U.1 U.2) L)).commutes

@[expose] def backward : ActualAffineDescentData318.Hom
    (CanonicalActualDescentFunctor318.datum Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) (original L U))
    (CanonicalActualDescentFunctor318.datum Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) (reconstructed f L U)) where
  sheafHom := (coveringIso f L U).inv
  commutes := OriginalAffineReconstructionUnit318.inverse_compatible Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1)
    (coveringIso f L U) (forward f L U).commutes

/-- The same original arbitrary base line is recovered on the actual
spectrum chart; no presentation equality or new local choice is assumed. -/
@[expose] def iso : (reconstructed f L U).object ≅ (original L U).object :=
  OriginalAffineMorphismDescent318.descendedIso Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1)
    (forward f L U) (backward f L U) (coveringIso f L U).hom_inv_id (coveringIso f L U).inv_hom_id

lemma iso_cover : (Scheme.Modules.pullback (AffineFaithfullyFlatChart318.map f U.1)).map
    (iso f L U).hom = (coveringIso f L U).hom :=
  OriginalAffineMorphismDescent318.descend_cover Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) (forward f L U)
end OriginalBaseLineAffineUnit318
