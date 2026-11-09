module
public import RelativeFppfLineLocal318
public section
noncomputable section
namespace RelativeFppfLineNeutral318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LineSheafClass318 RelativeLineClassQuotient318
open RelativeFppfLineSheaf318 RelativeFppfLineLocal318
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- Triviality in the original relative quotient means an actual original
line is isomorphic to the actual pullback of an original base line. -/
lemma relative_line_eq_one_iff (L : Line X) :
    classMap p (classOf L) = 1 ↔
      ∃ N : Line S, Nonempty ((LineSheafPullback318.line p N).object ≅ L.object) := by
  rw [classMap_eq_one_iff]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨N, rfl⟩ := Quotient.exists_rep d
    exact ⟨N, (classOf_eq_iff _ _).mp hd⟩
  · rintro ⟨N, hN⟩
    exact ⟨classOf N, (classOf_eq_iff _ _).mpr hN⟩

/-- The exact naive equality sieve, prior to sheafification. -/
@[expose] def neutralSieve (T : Over S) (L : Line (pullback p T.hom)) : Sieve T :=
  Presheaf.equalizerSieve
    (F := RelativeLineClassBaseChange318.presheaf p)
    (X := op T) (classMap (pullback.snd p T.hom) (classOf L)) 1

/-- An arrow of the neutral sieve is precisely an actual original sheaf
isomorphism after the full scheme-theoretic base change, modulo a base line. -/
lemma neutralSieve_iff {T V : Over S} (L : Line (pullback p T.hom)) (g : V ⟶ T) :
    neutralSieve p T L g ↔ ∃ N : Line V.left,
      Nonempty ((LineSheafPullback318.line (pullback.snd p V.hom) N).object ≅
        (LineSheafPullback318.line
          (RelativeLineClassBaseChange318.totalMap p T.hom V.hom g.left g.w) L).object) := by
  change classMap (pullback.snd p V.hom)
      (classOf (LineSheafPullback318.line
        (RelativeLineClassBaseChange318.totalMap p T.hom V.hom g.left g.w) L)) =
      (RelativeLineClassBaseChange318.presheaf p).map g.op 1 ↔ _
  rw [map_one]
  exact relative_line_eq_one_iff _ _

/-- A line with neutral image in the actual fppf sheaf is fppf-locally the
actual pullback of an original base line, with the actual isomorphisms above. -/
lemma neutralSieve_cover (T : Over S) (L : Line (pullback p T.hom))
    (h : lineImage p T L = 1) : neutralSieve p T L ∈ topology S T := by
  apply local_equality_cover p T (classMap (pullback.snd p T.hom) (classOf L)) 1
  simpa only [lineImage, map_one] using h

/-- Conversely, the original fppf sheaf's separatedness turns this exact
local original-line criterion into global neutrality in that sheaf. -/
lemma neutralSieve_cover_iff (T : Over S) (L : Line (pullback p T.hom)) :
    neutralSieve p T L ∈ topology S T ↔ lineImage p T L = 1 := by
  constructor
  · intro h
    have hs : Presieve.IsSeparated (topology S)
        ((sheaf p).obj ⋙ forget CommGrpCat.{u+1}) := by
      apply Presieve.IsSheaf.isSeparated
      rw [← isSheaf_iff_isSheaf_of_type]
      exact ((sheafCompose (topology S) (forget CommGrpCat.{u+1})).obj (sheaf p)).property
    apply (hs _ h).ext
    intro V g hg
    change (sheaf p).obj.map g.op (lineImage p T L) = (sheaf p).obj.map g.op 1
    have hn := congrArg ((unit p).app (op V))
      (show (RelativeLineClassBaseChange318.presheaf p).map g.op
          (classMap (pullback.snd p T.hom) (classOf L)) =
        (RelativeLineClassBaseChange318.presheaf p).map g.op 1 from hg)
    rw [map_one]
    have hnat := ConcreteCategory.congr_hom ((unit p).naturality g.op)
      (classMap (pullback.snd p T.hom) (classOf L))
    change (unit p).app (op V)
        ((RelativeLineClassBaseChange318.presheaf p).map g.op
          (classMap (pullback.snd p T.hom) (classOf L))) =
      (sheaf p).obj.map g.op (lineImage p T L) at hnat
    exact hnat.symm.trans (by simpa only [map_one] using hn)
  · exact neutralSieve_cover p T L
end RelativeFppfLineNeutral318
