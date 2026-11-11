module
public import ClosedFamilyCanonicalProperties318
public section
noncomputable section
namespace ContactSchemePointFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
/-- Structure-preserving points on an arbitrary coefficient scheme. -/
abbrev SchemePoint := {f : B ⟶ ContactProjectiveQuotientParameter318.scheme c n //
  f ≫ ContactProjectiveParameterStructure318.structureMap c n=b}
variable (x : SchemePoint c n b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "a" => ContactProjectiveParameterStructure318.structureMap c n
local notation "q" => ContactProjectiveUniversalGluing318.original c n
abbrev family := OriginalClosedFamilyRestriction318.family p a x.val q
abbrev toFamily := OriginalClosedFamilyRestriction318.toFamily p a x.val q
abbrev projection := OriginalClosedFamilyRestriction318.projection p a x.val q
abbrev into : family c n b x ⟶ pullback p b := OriginalClosedFamilyRestriction318.into p a b x.val x.property q
abbrev sourceMap := RelativeSchemeCoefficient318.map p a b x.val x.property
@[reassoc] lemma into_base : into c n b x ≫ pullback.snd p b=projection c n b x :=
  OriginalClosedFamilyRestriction318.into_base _ _ _ _ _ _
lemma cartesian : IsPullback (toFamily c n b x) (into c n b x) q (sourceMap c n b x) :=
  OriginalClosedFamilyRestriction318.cartesian _ _ _ _ _ _
instance closed : IsClosedImmersion (into c n b x) := inferInstance
instance finite : IsFinite (projection c n b x) := inferInstance
instance flat : Flat (projection c n b x) := inferInstance
instance presentation : LocallyOfFinitePresentation (projection c n b x) := inferInstance
lemma rank (z : B) : (projection c n b x).finrank z=n := by
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _
    (IsPullback.of_hasPullback (ContactProjectiveUniversalProjection318.projection c n) x.val)]
  exact ContactProjectiveUniversalRank318.rank c n _
/-- Extract the actual full original universal ideal over ANY coefficient
scheme, with all standard family hypotheses proved, not assumed. -/
@[expose] def extract : ContactSchemeHilbertData318.Data c n b := by
  letI : IsFinite (into c n b x ≫ pullback.snd p b) := by rw [into_base]; infer_instance
  letI : Flat (into c n b x ≫ pullback.snd p b) := by rw [into_base]; infer_instance
  letI : LocallyOfFinitePresentation (into c n b x ≫ pullback.snd p b) := by rw [into_base]; infer_instance
  refine {ideal := (into c n b x).ker,finite := inferInstance,flat := inferInstance,
    presentation := inferInstance,rank := ?_}
  intro z
  rw [ClosedFamilyCanonicalProperties318.rank,into_base]
  exact rank c n b x z
end ContactSchemePointFamily318
