module
public import ActualPrincipalOpenRestriction318
public section
noncomputable section
namespace PrincipalRestrictionEvaluation318
open Polynomial ActualPrincipalOpenRestriction318
variable {R A K : Type*} [CommRing R] [CommRing A] [Field K]

lemma source_ne_zero (g : R →+* A) (d : R) (b : A) (hbd : b ∣ g d)
    (v : R →+* K) (f : A →+* K) (hsquare : f.comp g = v) (hv : v d ≠ 0) : f b ≠ 0 := by
  obtain ⟨k,hk⟩ := hbd
  intro hb
  have he : f (g d) = v d := congrArg (fun h : R →+* K => h d) hsquare
  rw [hk,map_mul,hb,zero_mul] at he
  exact hv he.symm

/-- Literal whole localization restriction agrees at every algebra
point. This includes all inverse denominators, not only ring generators. -/
theorem restriction_square (b c : A) (hbc : b ∣ c) (f : A →+* K)
    (hb : f b ≠ 0) (hc : f c ≠ 0) :
    (IsLocalization.Away.lift c (g := f) (isUnit_iff_ne_zero.mpr hc)).comp
      (restriction b c hbc) =
        IsLocalization.Away.lift b (g := f) (isUnit_iff_ne_zero.mpr hb) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers b)
  ext a
  simp only [RingHom.comp_apply,restriction_source,IsLocalization.Away.lift_eq]

/-- The full coefficient square is preserved when evaluating at ANY
whole algebra point above the new base open. -/
theorem base_square (g : R →+* A) (d : R) (v : R →+* K) (f : A →+* K)
    (hsquare : f.comp g = v) (hv : v d ≠ 0)
    (hfd : f (g d) ≠ 0) :
    (IsLocalization.Away.lift (g d) (g := f) (isUnit_iff_ne_zero.mpr hfd)).comp
      (Localization.awayMap g d) =
        IsLocalization.Away.lift d (g := v) (isUnit_iff_ne_zero.mpr hv) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  ext r
  simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,IsLocalization.Away.lift_eq]
  exact congrArg (fun h : R →+* K => h r) hsquare

/-- Any whole-order polynomial equality produced by transfer recovers
the OLD localized function at every whole complex evaluation on the new
base open. Neither a primitive-root selection nor a component choice is
part of the statement. -/
theorem transferred_value (g : R →+* A) (d : R) (b t : A) (hbd : b ∣ g d)
    (a : Localization.Away b) (H : Polynomial (Localization.Away d))
    (hH : H.eval₂ (Localization.awayMap g d) (algebraMap A (Localization.Away (g d)) t) =
      restriction b (g d) hbd a)
    (v : R →+* K) (f : A →+* K) (hsquare : f.comp g = v) (hv : v d ≠ 0) :
    H.eval₂ (IsLocalization.Away.lift d (g := v) (isUnit_iff_ne_zero.mpr hv)) (f t) =
      IsLocalization.Away.lift b (g := f)
        (isUnit_iff_ne_zero.mpr (source_ne_zero g d b hbd v f hsquare hv)) a := by
  have hfd : f (g d) ≠ 0 := by
    change (f.comp g) d ≠ 0
    rwa [hsquare]
  let E := IsLocalization.Away.lift (g d) (g := f) (isUnit_iff_ne_zero.mpr hfd)
  have he := congrArg E hH
  rw [Polynomial.hom_eval₂,IsLocalization.Away.lift_eq,
    base_square g d v f hsquare hv hfd] at he
  have hr := restriction_square b (g d) hbd f (source_ne_zero g d b hbd v f hsquare hv) hfd
  exact he.trans (congrArg (fun k : Localization.Away b →+* K => k a) hr)
end PrincipalRestrictionEvaluation318
