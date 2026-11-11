module
public import FractionFiniteCoefficientLift318
public import ActualPrincipalOpenRestriction318
public section
noncomputable section
namespace FractionPrincipalCompatibility318
open FractionFiniteCoefficientLift318 ActualPrincipalOpenRestriction318
section Restriction
variable (R K:Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
/-- Restricting a literal principal open does not change its embedding
in the SAME original fraction field, on any element of that open. -/
theorem restriction_field (r s:R)(hr:r≠0)(hs:s≠0)(h:r∣s):
    (toField R K s hs).comp (restriction r s h)=toField R K r hr:=by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext a
  simp only [RingHom.comp_apply,restriction_source,toField_coefficient]

end Restriction
section Base
variable (R A F K:Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Field F] [Field K]
  [Algebra R F] [IsFractionRing R F] [Algebra A K] [IsFractionRing A K]
/-- The localized BASE coefficient map is pinned by its actual original
ring square. This compares whole principal-localization elements, not
only coefficients or selected points. No unrelated field algebra is
chosen to make the square hold. -/
theorem base_field (f:R→+*A)(κ:F→+*K)
    (hκ:∀a:R,κ (algebraMap R F a)=algebraMap A K (f a))
    (d:R)(hd:d≠0)(ha:f d≠0):
    (toField A K (f d) ha).comp (Localization.awayMap f d)=
      κ.comp (toField R F d hd):=by
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  ext a
  simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,toField_coefficient]
  exact (hκ a).symm
end Base
end FractionPrincipalCompatibility318
