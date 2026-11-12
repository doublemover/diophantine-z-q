module
public import ContactProjectiveUniversalIntersection318
public section
noncomputable section
namespace ContactProjectiveUniversalGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ)
local notation "Z" => ContactProjectiveUniversalAmbient318.localFamily c n
local notation "f" => ContactProjectiveUniversalAmbient318.localInto c n
local notation "q" a => ContactQuotientUniversalOriginal318.into c a n
local notation "u" => ContactProjectiveUniversalAmbient318.into c n
/-- Actual family intersections are open in BOTH original families. -/
instance intersection_open (a b : Chart) : IsOpenImmersion (pullback.fst (f a) (f b)) := by
  let h := ContactProjectiveUniversalIntersection318.cartesian c n a b
  have ho : IsOpenImmersion (h.isoPullback.inv ≫ ContactProjectiveUniversalIntersection318.left c n a b) := inferInstance
  simpa only [h.isoPullback_inv_fst] using ho
lemma restriction (a b : Chart) : IsPullback (pullback.snd (f a) (f b))
    (pullback.fst (f a) (f b) ≫ q a) (f b) (u a) := by
  let h := ContactProjectiveUniversalIntersection318.cartesian c n a b
  apply (ContactProjectiveUniversalIntersection318.restriction c n a b).of_iso h.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom,Category.comp_id] using h.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,h.isoPullback_hom_fst]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
/-- The ACTUAL global universal quotient family on the already constructed
original projective-source parameter scheme. Its chart overlaps are literal
fiber products in the unchanged original source ambient scheme. -/
abbrev family : Scheme := MonoFamilyGlueData318.scheme Z f
abbrev into (a : Chart) : Z a ⟶ family c n := MonoFamilyGlueData318.into Z f a
abbrev cover : (family c n).OpenCover := MonoFamilyGlueData318.cover Z f
abbrev original : family c n ⟶ ContactProjectiveUniversalAmbient318.scheme c n := MonoFamilyGlueData318.map Z f
@[reassoc] lemma into_original (a : Chart) : into c n a ≫ original c n=q a ≫ u a :=
  MonoFamilyGlueData318.into_map Z f a
lemma cartesian (a : Chart) : IsPullback (into c n a) (q a) (original c n) (u a) :=
  SchemeClosedCoverGluing318.cartesian (ContactProjectiveUniversalAmbient318.cover c n) Z
    (fun a => q a) (restriction c n) a
instance closed : IsClosedImmersion (original c n) :=
  SchemeClosedCoverGluing318.closed (ContactProjectiveUniversalAmbient318.cover c n) Z
    (fun a => q a) (restriction c n)
abbrev idealSheaf : (ContactProjectiveUniversalAmbient318.scheme c n).IdealSheafData := (original c n).ker
end ContactProjectiveUniversalGluing318
