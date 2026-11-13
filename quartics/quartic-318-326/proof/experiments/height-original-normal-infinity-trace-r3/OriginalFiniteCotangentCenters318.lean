module
public import OriginalFiniteCotangentComparison318
public section
noncomputable section
namespace OriginalFiniteCotangentCenters318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open OriginalFiniteCotangentComparison318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1)

/-- For every good place where the original t is integral, construct the
actual contact-chart center and derive the bound using the square of its
Dt-preserving cotangent-fiber comparison with the original rational frame.
No chart center, derivative nonvanishing or common-scalar premise remains. -/
theorem exists_bound (ht : IsLocalization.IsInteger (V c t v) (t:K c t)) (i : Fin 4) :
    ∃ (j : Fin 4)
      (φ : IntegralBranchCoordinates318.B (V c t v) (localTwists c t v hv) j →+* V c t v),
      (∀ a : IntegralSourceBranches318.SourceOrder (V c t v) (localTwists c t v hv),
        algebraMap (V c t v) (K c t) (φ (algebraMap _ _ a))=
          IntegralValuativeGenericPoint318.sourceMap (V c t v) (K c t) (localTwists c t v hv)
            (t:K c t) (roots c t) (local_root_equations c t v hv) a) ∧
      derivativeRatio c t hn v hv j φ i≠0 ∧
      (∀ n : Fin 2, v (![ContactBicanonicalPointHeight318.a0 c t hn i,
        ContactBicanonicalPointHeight318.a1 c t hn i] n)*
          (v ((derivativeRatio c t hn v hv j φ i)^2))⁻¹≤1) ∧
      max (v (ContactBicanonicalPointHeight318.a0 c t hn i))
        (v (ContactBicanonicalPointHeight318.a1 c t hn i))=
          v ((derivativeRatio c t hn v hv j φ i)^2) := by
  obtain ⟨j,φ,hφ,hroot⟩ := OriginalPointFinitePlaceCenter318.branch_center c t v hv ht
  have h := original_bounds c t hn v hv j φ hφ i
  exact ⟨j,φ,hφ,derivativeRatio_ne c t hn v hv j φ hφ i,h.1,h.2⟩
end OriginalFiniteCotangentCenters318
