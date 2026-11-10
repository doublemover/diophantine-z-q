module
public import OriginalBaseLineUnitCompatibility318
public section
noncomputable section
namespace OriginalGlobalBaseUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalBaseLineUnitCompatibility318
set_option maxHeartbeats 3000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (L : Line Y)

/-- The base-side comparison is glued on the entire original affine
basis. Its inverse is glued separately by the existing original module
isomorphism construction, so it is an actual sheaf isomorphism. -/
@[expose] def iso : (reconstructed f L).object ≅ L.object :=
  InverseImageBasisIsoGluing318.iso (𝟙 Y) (reconstructed f L).object L.object
    (overIso f L) (overIso_nested f L)

lemma restricted_hom (U : Y.affineOpens) :
    (Scheme.Modules.restrictFunctor U.1.ι).map (iso f L).hom = (restriction f L U).hom := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  have hW : U.1.ι ''ᵁ W ≤ U.1 := by simpa using U.1.ι.image_le_opensRange W
  have hh := InverseImageBasisIsoGluing318.hom_component (𝟙 Y) (reconstructed f L).object L.object
    (overIso f L) (overIso_nested f L) U (U.1.ι ''ᵁ W) hW s
  change (iso f L).hom.app (U.1.ι ''ᵁ W) s = (restriction f L U).hom.app W s
  rw [hh]
  exact OpenSheafRestrictionCompatibility318.toOver_hom_app (restriction f L U) W s

lemma pullback_chart (U : Y.affineOpens) :
    (Scheme.Modules.pullback U.1.ι).map (iso f L).hom =
      (OriginalBaseLineOpenUnit318.comparison f L U).hom := by
  apply (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).hom.app
    (reconstructed f L).object)).mp
  rw [← (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).hom.naturality (iso f L).hom,
    restricted_hom]
  simp only [restriction,PullbackRestrictionCompatibility318.restriction,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,Iso.app_inv,Category.assoc,Iso.inv_hom_id_app,Category.comp_id]

/-- Pulling back the actual base-side unit gives exactly the original
specified global reconstruction comparison, with scalar one. -/
lemma iso_cover : (Scheme.Modules.pullback f).map (iso f L).hom =
    (AffineMorphismGlobalRecovery318.comparison f (datum f L)).hom := by
  apply ModuleRestrictionCoverFaithful318.hom_ext (AffineOriginalCoverComparison318.sourceOpen f)
    (AffineOriginalCoverComparison318.cover f)
  intro U
  let a := (AffineOriginalCoverComparison318.sourceOpen f U).ι
  let c := ActualDescentBaseChangeDiagram318.coverComparison f (f ∣_ U.1) a U.1.ι
    (morphismRestrict_ι f U.1).symm
  have hn := c.hom.naturality (iso f L).hom
  simp only [Functor.comp_map] at hn
  rw [pullback_chart] at hn
  have hh := OriginalBaseLineOpenUnit318.comparison_cover f L U
  have hp : (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback f).map (iso f L).hom) =
      (Scheme.Modules.pullback a).map (AffineMorphismGlobalRecovery318.comparison f (datum f L)).hom := by
    apply (cancel_mono (c.hom.app L.object)).mp
    exact hn.trans hh
  let d := Scheme.Modules.restrictFunctorIsoPullback a
  apply (cancel_mono (d.hom.app ((Scheme.Modules.pullback f).obj L.object))).mp
  rw [d.hom.naturality,d.hom.naturality,hp]

lemma iso_cover_iso : (Scheme.Modules.pullback f).mapIso (iso f L) =
    AffineMorphismGlobalRecovery318.comparison f (datum f L) :=
  Iso.ext (iso_cover f L)

variable {L}
/-- Naturality on all original base maps follows from exact covering
recovery and the independently proved original faithfully flat detector. -/
lemma natural {K : Line Y} (g : L.object ⟶ K.object) :
    AffineGlobalMorphismEffectivity318.map f (OriginalCanonicalDescent318.map f g) ≫
      (iso f K).hom = (iso f L).hom ≫ g := by
  apply GlobalAffineLineFaithfulness318.pullback_injective f
  rw [Functor.map_comp,Functor.map_comp,iso_cover,iso_cover]
  exact AffineGlobalMapCoverSquare318.cover_square f (OriginalCanonicalDescent318.map f g)
end OriginalGlobalBaseUnit318
