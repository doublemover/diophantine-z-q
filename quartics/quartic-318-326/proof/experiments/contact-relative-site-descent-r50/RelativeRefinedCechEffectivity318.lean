module
public import OriginalLineRefinementIso318
public section
noncomputable section
namespace RelativeRefinedCechEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
open RigidifiedRelativeClass318 RelativeLineClassQuotient318 RigidifiedCechNerve318
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (pointed : e' ≫ f = g ≫ e)
  (p : X ⟶ S) (p' : X' ⟶ S') (square : f ≫ p = p' ≫ g)
  (hs : e ≫ p = 𝟙 S) (hs' : e' ≫ p' = 𝟙 S')
  (r : ActualAffineBaseRefinement318.Refinement f)

include hs hs' r in
/-- The original relative map is separated when the total cover admits
an actual affine faithfully flat refinement; f itself need not be affine. -/
lemma map_injective (hl : Function.Bijective e'.appTop)
    (hd : Function.Injective (doubleSection f g e e' pointed).appTop) :
    Function.Injective (RelativeLineClassQuotient318.map p p' f g square) := by
  intro c d h
  let L := RigidifiedClassQuotient318.representative e p hs c
  let M := RigidifiedClassQuotient318.representative e p hs d
  have hc := RigidifiedClassQuotient318.representative_class e p hs c
  have hd' := RigidifiedClassQuotient318.representative_class e p hs d
  have heq : relativeClass p' e' (RigidifiedCanonicalOverlap318.pulled f g e e' pointed L) =
      relativeClass p' e' (RigidifiedCanonicalOverlap318.pulled f g e e' pointed M) := by
    rw [RigidifiedPointedPullback318.relativeClass_line e e' f g pointed p p' square,
      RigidifiedPointedPullback318.relativeClass_line e e' f g pointed p p' square,hc,hd']
    exact h
  obtain ⟨a⟩ := (relative_eq_iff_compatible p' e' hs' hl _ _).mp heq
  let k := RigidifiedCanonicalIsoDescent318.hom f g e e' pointed a hd
  have hi := OriginalLineRefinementIso318.iso f r a.iso k rfl
  have he := congrArg (classMap p) (LineSheafClass318.classOf_eq hi)
  change relativeClass p e L = relativeClass p e M at he
  exact hc.symm.trans (he.trans hd')

include hs hs' r in
/-- The actual original relative-class matching problem is uniquely
effective through the supplied original refinement, retaining the original
f-overlap rather than only its restriction to that refinement. -/
theorem matching_unique (hl : Function.Bijective e'.appTop)
    (hd : Function.Bijective (doubleSection f g e e' pointed).appTop)
    (ht : Function.Injective (tripleSection f g e e' pointed).appTop)
    (c : RelativeClass p')
    (hm : RelativeCechClassEffectivity318.firstMap f g p p' square c =
      RelativeCechClassEffectivity318.secondMap f g p p' square c) :
    ∃! d : RelativeClass p, RelativeLineClassQuotient318.map p p' f g square d = c := by
  let D := RelativeCechClassEffectivity318.datum f g e e' pointed p p' square hs' c hm hd hl.injective ht
  let L := RefinedCoverObjectEffectivity318.line f r.map r.lift r.factor D
  let d := classMap p (classOf L)
  have he := congrArg (classMap p') (LineSheafClass318.classOf_eq
    (RefinedCoverObjectEffectivity318.comparison f r.map r.lift r.factor D))
  change RelativeLineClassQuotient318.map p p' f g square d =
    relativeClass p' e' (RigidifiedClassQuotient318.representative e' p' hs' c) at he
  have hdc : RelativeLineClassQuotient318.map p p' f g square d = c :=
    he.trans (RigidifiedClassQuotient318.representative_class e' p' hs' c)
  exact ⟨d,hdc,fun d' hd' => map_injective f g e e' pointed p p' square hs hs' r
    hl hd.injective (hd'.trans hdc.symm)⟩
end RelativeRefinedCechEffectivity318
