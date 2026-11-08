module
public import GammaHAction318
public section
noncomputable section
open Function Filter Topology TopologicalSpace UpperHalfPlane
open DerivativeCocycle318 PeterssonQuotient318 GammaHGroup318 GammaHDiamond318 GammaHAction318
open scoped MatrixGroups
namespace GammaHDiamondQuotient318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

variable (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
local instance : MulAction H (Fine N) := diamondAction N H
local instance : ContinuousConstSMul H (Fine N) := diamond_continuous N H

abbrev DiamondQuotient := MulAction.orbitRel.Quotient H (Fine N)
@[expose] def quotient : Fine N→DiamondQuotient N H :=
  Quotient.mk (MulAction.orbitRel H (Fine N))

/-- Forgetting the marking is invariant under the actual finite diamond action. -/
theorem forget_action (u:H) (q:Fine N) :
    GammaHQuotient318.forget N H (u•q)=GammaHQuotient318.forget N H q := by
  obtain ⟨g,rfl⟩ := diamond_surjective N H u
  induction q using Quotient.inductionOn with
  | h tau =>
    have hd : diamond N H g • GammaOneAtlas318.quotientMap N tau=
        GammaOneAtlas318.quotientMap N (g.val•tau) := diamond_projection N H g tau
    change GammaHQuotient318.forget N H (diamond N H g • GammaOneAtlas318.quotientMap N tau)=
      GammaHQuotient318.forget N H (GammaOneAtlas318.quotientMap N tau)
    rw [hd,GammaHQuotient318.forget_projection,GammaHQuotient318.forget_projection]
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact ⟨⟨GammaHQuotient318.positiveMatrix N H g,⟨g,rfl⟩⟩,rfl⟩

@[expose] def toActual : DiamondQuotient N H→GammaHQuotient318.Curve N H :=
  Quotient.lift (GammaHQuotient318.forget N H) (by
    intro a b hab
    obtain ⟨u,hu⟩:=MulAction.orbitRel_apply.mp hab
    rw [←hu]
    exact forget_action N H u b)

@[expose] def fromActual : GammaHQuotient318.Curve N H→DiamondQuotient N H :=
  Quotient.lift (fun tau=>quotient N H (GammaOneAtlas318.quotientMap N tau)) (by
    intro a b hab
    obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp hab
    obtain ⟨gamma,hgamma⟩:=g.property
    have he : gamma.val•b=a := by
      change (g.val:G)•b=a at hg
      rw [←hgamma] at hg
      exact hg
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨diamond N H gamma,?_⟩
    change diamond N H gamma • GammaOneAtlas318.quotientMap N b=
      GammaOneAtlas318.quotientMap N a
    exact (diamond_projection N H gamma b).trans (congrArg (GammaOneAtlas318.quotientMap N) he))

theorem toActual_quotient (q:Fine N) :
    toActual N H (quotient N H q)=GammaHQuotient318.forget N H q := rfl

theorem fromActual_projection (tau:UpperHalfPlane) :
    fromActual N H (GammaHQuotient318.projection N H tau)=
      quotient N H (GammaOneAtlas318.quotientMap N tau) := rfl

theorem toActual_continuous : Continuous (toActual N H) :=
  continuous_quot_lift _ (GammaHQuotient318.forget_continuous N H)

theorem fromActual_continuous : Continuous (fromActual N H) :=
  continuous_quot_lift _ (continuous_quot_mk.comp continuous_quot_mk)

/-- The quotient of the actual fine analytic source by the actual H diamond
action is homeomorphic to the actual Gamma_H orbit quotient. All maps are
the genuine forgetful maps, with their original quotient topologies. -/
@[expose] def actualHomeomorph : DiamondQuotient N H ≃ₜ GammaHQuotient318.Curve N H where
  toFun:=toActual N H
  invFun:=fromActual N H
  left_inv q:=by
    induction q using Quotient.inductionOn with
    | h q =>
      induction q using Quotient.inductionOn with
      | h tau => rfl
  right_inv q:=by
    induction q using Quotient.inductionOn with
    | h tau => rfl
  continuous_toFun:=toActual_continuous N H
  continuous_invFun:=fromActual_continuous N H

/-- Genuine j is preserved by the actual analytic H-quotient comparison. -/
theorem actualHomeomorph_j (q:Fine N) :
    GammaHQuotient318.jMap N H (actualHomeomorph N H (quotient N H q))=QuotientJ318.jMap N q :=
  GammaHQuotient318.jMap_forget N H q

end GammaHDiamondQuotient318
