module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

public section
noncomputable section
namespace SchemeIsoPushforwardRecovery318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules)

/-- On an actual scheme isomorphism, the original restriction unit is an
isomorphism because every original image-preimage open is the same open. -/
instance restrictionUnit_isIso : IsIso ((Scheme.Modules.restrictAdjunction f).unit.app M) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  have he : f ''ᵁ (f ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Hom.opensRange_of_isIso,top_inf_eq]
  have hg : homOfLE (f.image_preimage_le U) = eqToHom he := Subsingleton.elim _ _
  rw [Scheme.Modules.restrictAdjunction_unit_app_app,hg]
  change IsIso ((M.presheaf.mapIso (eqToIso he).op).hom)
  infer_instance

/-- Recover the SAME original sheaf after its actual pullback and pushforward
along an actual scheme isomorphism. -/
@[expose] def recovery :
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) ≅ M :=
  (asIso ((Scheme.Modules.restrictAdjunction f).unit.app M) ≪≫
    (Scheme.Modules.pushforward f).mapIso ((Scheme.Modules.restrictFunctorIsoPullback f).app M)).symm

variable (p : Y ⟶ Z) (q : X ⟶ Z) (h : f ≫ p = q)

/-- The original entire base pushforward is preserved, with its displayed
original base map, not merely the underlying additive global sections. -/
def overBase : (Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback f).obj M) ≅
    (Scheme.Modules.pushforward p).obj M :=
  (Scheme.Modules.pushforwardCongr h.symm).app ((Scheme.Modules.pullback f).obj M) ≪≫
    ((Scheme.Modules.pushforwardComp f p).app ((Scheme.Modules.pullback f).obj M)).symm ≪≫
    (Scheme.Modules.pushforward p).mapIso (recovery f M)
end SchemeIsoPushforwardRecovery318
