module
public import RelativeFppfLineSheaf318
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public section
noncomputable section
namespace RelativeFppfLineLocal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RelativeFppfLineSheaf318 RelativeLineClassQuotient318
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S)

instance unit_locallySurjective : Presheaf.IsLocallySurjective (topology S) (unit p) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (topology S)
    (toSheafify (topology S) (RelativeLineClassBaseChange318.presheaf p)))

instance unit_locallyInjective : Presheaf.IsLocallyInjective (topology S) (unit p) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (topology S)
    (toSheafify (topology S) (RelativeLineClassBaseChange318.presheaf p)))

/-- Every naive relative class has a representative which is an actual line
on the actual whole scheme fiber product. -/
lemma original_line_surjective (T : Over S) : Function.Surjective
    (fun L : LineSheafClass318.Line (pullback p T.hom) =>
      classMap (pullback.snd p T.hom) (LineSheafClass318.classOf L)) := by
  intro c
  obtain ⟨d, rfl⟩ := classMap_surjective (pullback.snd p T.hom) c
  obtain ⟨L, rfl⟩ := Quotient.exists_rep d
  exact ⟨L, rfl⟩

/-- The canonical fppf class of an original line, through the exact two original
quotients and the universal sheafification map. -/
@[expose] def lineImage (T : Over S)
    (L : LineSheafClass318.Line (pullback p T.hom)) : (sheaf p).obj.obj (op T) :=
  (unit p).app (op T) (classMap (pullback.snd p T.hom) (LineSheafClass318.classOf L))

lemma local_original_line_iff {T V : Over S} (s : (sheaf p).obj.obj (op T)) (g : V ⟶ T) :
    Presheaf.imageSieve (unit p) s g ↔
      ∃ L : LineSheafClass318.Line (pullback p V.hom),
        lineImage p V L = (sheaf p).obj.map g.op s := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨L, rfl⟩ := original_line_surjective p V c
    exact ⟨L, hc⟩
  · rintro ⟨L, hL⟩
    exact ⟨classMap (pullback.snd p V.hom) (LineSheafClass318.classOf L), hL⟩

/-- Every section is represented by actual original line bundles on an fppf
covering sieve. No global representative or field-only reduction is asserted. -/
lemma local_original_lines_cover (T : Over S) (s : (sheaf p).obj.obj (op T)) :
    Presheaf.imageSieve (unit p) s ∈ topology S T :=
  Presheaf.imageSieve_mem (topology S) (unit p) s

/-- Equal fppf images of naive classes agree after an actual fppf cover. -/
lemma local_equality_cover (T : Over S)
    (c d : (RelativeLineClassBaseChange318.presheaf p).obj (op T))
    (h : (unit p).app (op T) c = (unit p).app (op T) d) :
    Presheaf.equalizerSieve c d ∈ topology S T :=
  Presheaf.equalizerSieve_mem (topology S) (unit p) c d h
end RelativeFppfLineLocal318
