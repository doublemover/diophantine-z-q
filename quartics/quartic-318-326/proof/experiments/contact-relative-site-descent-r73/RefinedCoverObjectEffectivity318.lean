module
public import MixedOriginalDescentCompatibility318
public section
noncomputable section
namespace RefinedCoverObjectEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318 ActualOverlapDiagram318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
  (D : Datum f)
abbrev line := MixedCoverRecovery318.baseLine f g a factor D
abbrev comparison := MixedCoverCompatibleRecovery318.recovery f g a factor D

/-- The recovered whole-X comparison preserves the genuine original
f-double overlap. Equality is detected after refining both endpoints by
the actual mixed affine faithfully flat cover. -/
lemma commutes : (OriginalCanonicalDescent318.datum f (line f g a factor D)).overlap ≫
    (Scheme.Modules.pullback (second f)).map (comparison f g a factor D).hom =
  (Scheme.Modules.pullback (first f)).map (comparison f g a factor D).hom ≫ D.overlap := by
  let p := MixedCoverRecovery318.first f g
  let h := MixedOriginalDescentCompatibility318.arrow f g
  let square := MixedOriginalDescentCompatibility318.first_square f g
  let c := RefinementDoubleCover318.double f p
  let C := OriginalCanonicalDescent318.datum f (line f g a factor D)
  apply GlobalAffineLineFaithfulness318.pullback_injective c
    (L:=LineSheafPullback318.line (first f) C.line)
    (K:=LineSheafPullback318.line (second f) D.line)
  apply OriginalDescentSquareReflection318.pullback_square f h p (𝟙 Y) square C D
    (comparison f g a factor D).hom
  have hc := (MixedOriginalDescentCompatibility318.hom f g a factor D).commutes
  have he := congrArg Iso.hom (MixedCoverCompatibleRecovery318.recovery_cover f g a factor D)
  simp only [Functor.mapIso_hom] at he
  rw [MixedOriginalDescentCompatibility318.hom_comparison,← he] at hc
  exact hc

@[expose] def hom : Hom (OriginalCanonicalDescent318.datum f (line f g a factor D)) D where
  sheafHom := (comparison f g a factor D).hom
  commutes := commutes f g a factor D

@[expose] def inverse : Hom D (OriginalCanonicalDescent318.datum f (line f g a factor D)) :=
  OriginalCanonicalDescent318.inverse f (comparison f g a factor D) (commutes f g a factor D)

lemma hom_inverse : (hom f g a factor D).comp (inverse f g a factor D) =
    Hom.id (OriginalCanonicalDescent318.datum f (line f g a factor D)) :=
  Hom.ext (comparison f g a factor D).hom_inv_id
lemma inverse_hom : (inverse f g a factor D).comp (hom f g a factor D) = Hom.id D :=
  Hom.ext (comparison f g a factor D).inv_hom_id

include factor in
/-- Genuine effective original line descent for every arrow admitting
an explicitly supplied affine faithfully flat refinement. Both the line
on the whole base and its original f-double compatible recovery are built. -/
theorem effective : ∃ L : Line Y, ∃ e : (Scheme.Modules.pullback f).obj L.object ≅ D.line.object,
    (OriginalCanonicalDescent318.datum f L).overlap ≫
      (Scheme.Modules.pullback (second f)).map e.hom =
    (Scheme.Modules.pullback (first f)).map e.hom ≫ D.overlap :=
  ⟨line f g a factor D,comparison f g a factor D,commutes f g a factor D⟩
end RefinedCoverObjectEffectivity318
