module
public import OriginalDescentSquareReflection318
public section
noncomputable section
namespace AffineMorphismGlobalEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318 ActualOverlapDiagram318
set_option maxHeartbeats 3000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : Datum f)
abbrev line := AffineMorphismGlobalLine318.line f D
abbrev comparison := AffineMorphismGlobalRecovery318.comparison f D

/-- The specific globally glued original comparison respects the genuine
original categorical double overlap. This is detected on the full original
restricted doubles, not assumed as a global gluing condition. -/
lemma comparison_commutes :
    CanonicalSheafOverlap318.actual (line f D).object f ≫
      (Scheme.Modules.pullback (second f)).map (comparison f D).hom =
    (Scheme.Modules.pullback (first f)).map (comparison f D).hom ≫ D.overlap := by
  apply OriginalDoubleCoverFaithful318.hom_ext f
  intro U
  have hh := (OriginalLocalRecoveryDescent318.comparisonHom f D U).commutes
  rw [OriginalLocalRecoveryDescent318.comparisonHom_map] at hh
  have hp := congrArg Iso.hom (GlobalComparisonRestriction318.pullback_iso f D U)
  simp only [Functor.mapIso_hom] at hp
  rw [← hp] at hh
  exact OriginalDescentSquareReflection318.pullback_square f (f ∣_ U.1)
    (AffineOriginalCoverComparison318.sourceOpen f U).ι U.1.ι (morphismRestrict_ι f U.1).symm
    (OriginalCanonicalDescent318.datum f (line f D)) D (comparison f D).hom hh

@[expose] def hom : Hom (OriginalCanonicalDescent318.datum f (line f D)) D where
  sheafHom := (comparison f D).hom
  commutes := comparison_commutes f D

@[expose] def inverse : Hom D (OriginalCanonicalDescent318.datum f (line f D)) :=
  OriginalCanonicalDescent318.inverse f (comparison f D) (comparison_commutes f D)

lemma hom_inverse : (hom f D).comp (inverse f D) = Hom.id _ :=
  Hom.ext (comparison f D).hom_inv_id

lemma inverse_hom : (inverse f D).comp (hom f D) = Hom.id _ :=
  Hom.ext (comparison f D).inv_hom_id

/-- Effective original line descent for an affine faithfully flat covering
morphism over an arbitrary base scheme, retaining the exact original line,
overlap and specified globally reconstructed comparison. -/
theorem effective : ∃ L : Line Y, ∃ e : (Scheme.Modules.pullback f).obj L.object ≅ D.line.object,
    CanonicalSheafOverlap318.actual L.object f ≫ (Scheme.Modules.pullback (second f)).map e.hom =
      (Scheme.Modules.pullback (first f)).map e.hom ≫ D.overlap :=
  ⟨line f D,comparison f D,comparison_commutes f D⟩
end AffineMorphismGlobalEffectivity318
