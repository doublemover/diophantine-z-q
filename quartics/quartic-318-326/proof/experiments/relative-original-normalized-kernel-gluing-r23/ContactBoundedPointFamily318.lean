module
public import ContactBoundedClassifyingMap318
public section
noncomputable section
namespace ContactBoundedPointFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
/-- Bounded-rank parameter points on arbitrary coefficient schemes. -/
abbrev SchemePoint := {f : B ⟶ ContactBoundedHilbertParameter318.scheme c N //
  f ≫ ContactBoundedHilbertParameter318.structureMap c N=b}
variable (x : SchemePoint c N b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "a" => ContactBoundedHilbertParameter318.structureMap c N
local notation "q" => ContactBoundedUniversalFamily318.original c N
abbrev family := OriginalClosedFamilyRestriction318.family p a x.val q
abbrev toFamily := OriginalClosedFamilyRestriction318.toFamily p a x.val q
abbrev projection := OriginalClosedFamilyRestriction318.projection p a x.val q
abbrev into : family c N b x ⟶ pullback p b := OriginalClosedFamilyRestriction318.into p a b x.val x.property q
abbrev sourceMap := RelativeSchemeCoefficient318.map p a b x.val x.property
@[reassoc] lemma into_base : into c N b x ≫ pullback.snd p b=projection c N b x :=
  OriginalClosedFamilyRestriction318.into_base _ _ _ _ _ _
lemma cartesian : IsPullback (toFamily c N b x) (into c N b x) q (sourceMap c N b x) :=
  OriginalClosedFamilyRestriction318.cartesian _ _ _ _ _ _
instance closed : IsClosedImmersion (into c N b x) := inferInstance
instance finite : IsFinite (projection c N b x) := inferInstance
instance flat : Flat (projection c N b x) := inferInstance
instance presentation : LocallyOfFinitePresentation (projection c N b x) := inferInstance
lemma rank (z : B) : (projection c N b x).finrank z=
    (ContactBoundedHilbertParameter318.projection c N).finrank (x.val z) := by
  have h := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (IsPullback.of_hasPullback (q ≫ pullback.snd p a) x.val) z
  simpa only [ContactBoundedUniversalFamily318.original_snd] using h
lemma bound (z : B) : (projection c N b x).finrank z≤N := by
  rw [rank]
  exact ContactBoundedHilbertParameter318.rank_bound c N _
/-- Extract the actual full original universal ideal over ANY coefficient
scheme, with finite flat finite presentation and the bound proved, not assumed. -/
@[expose] def extract : ContactBoundedSchemeHilbertData318.Data c N b := by
  letI : IsFinite (into c N b x ≫ pullback.snd p b) := by rw [into_base]; infer_instance
  letI : Flat (into c N b x ≫ pullback.snd p b) := by rw [into_base]; infer_instance
  letI : LocallyOfFinitePresentation (into c N b x ≫ pullback.snd p b) := by rw [into_base]; infer_instance
  refine {ideal := (into c N b x).ker,finite := inferInstance,flat := inferInstance,
    presentation := inferInstance,bound := ?_}
  intro z
  rw [ClosedFamilyCanonicalProperties318.rank,into_base]
  exact bound c N b x z
end ContactBoundedPointFamily318
