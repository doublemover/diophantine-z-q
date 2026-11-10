module
public import AffineMorphismGlobalEffectivity318
public section
noncomputable section
namespace GlobalAffineLineFaithfulness318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  {L K : Line Y} (a b : L.object ⟶ K.object)
  (h : (Scheme.Modules.pullback f).map a = (Scheme.Modules.pullback f).map b)

include h in
lemma affine_chart (U : Y.affineOpens) :
    (Scheme.Modules.pullback U.2.fromSpec).map a = (Scheme.Modules.pullback U.2.fromSpec).map b := by
  letI := AffineFaithfullyFlatChart318.algebra f U.1
  letI : Module.FaithfullyFlat Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) :=
    AffineFaithfullyFlatChart318.module_faithfullyFlat f U.1 U.2
  apply OriginalAffineLineFaithfulness318.pullback_map_injective Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1)
    (L:=LineSheafPullback318.line U.2.fromSpec L) (K:=LineSheafPullback318.line U.2.fromSpec K)
  let c := ActualDescentBaseChangeDiagram318.coverComparison f
    (AffineFaithfullyFlatChart318.map f U.1) (AffineFaithfullyFlatChart318.source f U.1 U.2)
    U.2.fromSpec (AffineFaithfullyFlatChart318.square f U.1 U.2)
  apply (cancel_epi (c.hom.app L.object)).mp
  have ha := c.hom.naturality a
  have hb := c.hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← ha,← hb,h]

include h in
lemma restriction_chart (U : Y.affineOpens) :
    (Scheme.Modules.restrictFunctor U.1.ι).map a = (Scheme.Modules.restrictFunctor U.1.ι).map b := by
  let q := PullbackPathComposition318.iso U.2.isoSpec.hom U.2.fromSpec U.1.ι U.2.isoSpec_hom_fromSpec
  have ht := congrArg (fun z => (Scheme.Modules.pullback U.2.isoSpec.hom).map z ≫ q.hom.app K.object)
    (affine_chart f a b h U)
  have ha := q.hom.naturality a
  have hb := q.hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [ha,hb] at ht
  have hp := (cancel_epi (q.hom.app L.object)).mp ht
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).hom.app K.object)).mp
  rw [(Scheme.Modules.restrictFunctorIsoPullback U.1.ι).hom.naturality a,
    (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).hom.naturality b,hp]

include h in
/-- Original faithfully flat pullback detects maps of arbitrary original
line sheaves over the whole, possibly non-affine base. -/
lemma pullback_injective : a = b :=
  ModuleRestrictionCoverFaithful318.hom_ext (fun U : Y.affineOpens => U.1)
    (AffineMorphismGlobalLine318.cover (Y:=Y)) (restriction_chart f a b h)
end GlobalAffineLineFaithfulness318
