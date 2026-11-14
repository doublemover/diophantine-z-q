module
public import ContactProjectiveUniversalGluing318
public section
noncomputable section
namespace ContactProjectiveUniversalProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ)
local notation "q" => ContactProjectiveUniversalGluing318.original c n
local notation "p" => ContactProjectiveUniversalAmbient318.projection c n
abbrev projection : ContactProjectiveUniversalGluing318.family c n ⟶
    ContactProjectiveQuotientParameter318.scheme c n := q ≫ p
@[reassoc] lemma into_projection (a : Chart) : ContactProjectiveUniversalGluing318.into c n a ≫ projection c n=
    ContactQuotientUniversalOriginal318.projection c a n ≫ ContactProjectiveQuotientParameter318.into c n a := by
  rw [projection,← Category.assoc,ContactProjectiveUniversalGluing318.into_original,Category.assoc,
    RelativeSchemeCoefficient318.map_snd,← Category.assoc,ContactQuotientUniversalOriginal318.into_base]
/-- Each entire affine-source universal family is the true Cartesian
restriction of the global universal family on the actual parameter chart. -/
lemma cartesian (a : Chart) : IsPullback (ContactProjectiveUniversalGluing318.into c n a)
    (ContactQuotientUniversalOriginal318.projection c a n) (projection c n)
    (ContactProjectiveQuotientParameter318.into c n a) := by
  have h := (ContactProjectiveUniversalGluing318.cartesian c n a).paste_vert
    (ContactProjectiveUniversalAmbient318.cartesian c n a)
  simpa only [ContactQuotientUniversalOriginal318.into_base] using h
instance finite : IsFinite (projection c n) := by
  apply IsZariskiLocalAtTarget.of_openCover (ContactProjectiveQuotientParameter318.cover c n)
  intro a
  rw [← (cartesian c n a).isoPullback_inv_snd]
  infer_instance
instance flat : Flat (projection c n) := by
  apply IsZariskiLocalAtTarget.of_openCover (ContactProjectiveQuotientParameter318.cover c n)
  intro a
  rw [← (cartesian c n a).isoPullback_inv_snd]
  infer_instance
instance presentation : LocallyOfFinitePresentation (projection c n) := by
  apply IsZariskiLocalAtTarget.of_openCover (ContactProjectiveQuotientParameter318.cover c n)
  intro a
  rw [← (cartesian c n a).isoPullback_inv_snd]
  infer_instance
end ContactProjectiveUniversalProjection318
