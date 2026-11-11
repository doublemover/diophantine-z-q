module
public import OriginalInfinityCotangentComparison318
public section
noncomputable section
namespace OriginalGoodPlaceCotangentNorms318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1) (i : Fin 4)

/-- Provenance of a local normalizer: it is the square of the actual
Dt-preserving comparison, either on a genuine contact-chart center or on
the full infinity chart of the SAME signed-root point. -/
@[expose] def DifferentialNormalization (α : K c t) : Prop :=
  (∃ (j : Fin 4)
    (φ : IntegralBranchCoordinates318.B (V c t v) (localTwists c t v hv) j →+* V c t v),
    (∀ a : IntegralSourceBranches318.SourceOrder (V c t v) (localTwists c t v hv),
      algebraMap (V c t v) (K c t) (φ (algebraMap _ _ a))=
        IntegralValuativeGenericPoint318.sourceMap (V c t v) (K c t) (localTwists c t v hv)
          (t:K c t) (roots c t) (local_root_equations c t v hv) a) ∧
    α=(OriginalFiniteCotangentComparison318.derivativeRatio c t hn v hv j φ i)^2) ∨
  (∃ ht : ¬IsLocalization.IsInteger (V c t v) (t:K c t),
    α=(OriginalInfinityCotangentComparison318.derivativeRatio c t hn v hv ht i)^2)

/-- Exhaustive good-place differential norm construction. The finite and
infinity cases both use actual relative cotangent-fiber comparisons. -/
theorem exists_normalization : ∃ α : K c t,
    DifferentialNormalization c t hn v hv i α ∧ α≠0 ∧
    (∀ n : Fin 2, v (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*(v α)⁻¹≤1) ∧
    max (v (ContactBicanonicalPointHeight318.a0 c t hn i))
      (v (ContactBicanonicalPointHeight318.a1 c t hn i))=v α := by
  by_cases ht : IsLocalization.IsInteger (V c t v) (t:K c t)
  · obtain ⟨j,φ,hφ,hne,hb,hm⟩ := OriginalFiniteCotangentCenters318.exists_bound c t hn v hv ht i
    exact ⟨(OriginalFiniteCotangentComparison318.derivativeRatio c t hn v hv j φ i)^2,
      Or.inl ⟨j,φ,hφ,rfl⟩,pow_ne_zero 2 hne,hb,hm⟩
  · have h := OriginalInfinityCotangentComparison318.original_bounds c t hn v hv ht i
    exact ⟨(OriginalInfinityCotangentComparison318.derivativeRatio c t hn v hv ht i)^2,
      Or.inr ⟨ht,rfl⟩,pow_ne_zero 2 (OriginalInfinityCotangentComparison318.derivativeRatio_ne c t hn v hv ht i),
      h.1,h.2⟩

/-- Choose only after constructing and identifying an actual differential
normalization on a full original chart. -/
@[expose] def normalizer : K c t := Classical.choose (exists_normalization c t hn v hv i)
theorem normalizer_provenance : DifferentialNormalization c t hn v hv i (normalizer c t hn v hv i) :=
  (Classical.choose_spec (exists_normalization c t hn v hv i)).1
theorem normalizer_ne : normalizer c t hn v hv i≠0 :=
  (Classical.choose_spec (exists_normalization c t hn v hv i)).2.1
theorem normalizer_max :
    max (v (ContactBicanonicalPointHeight318.a0 c t hn i))
      (v (ContactBicanonicalPointHeight318.a1 c t hn i))=v (normalizer c t hn v hv i) :=
  (Classical.choose_spec (exists_normalization c t hn v hv i)).2.2.2
@[expose] def finiteNorm : ℝ := (v (normalizer c t hn v hv i))⁻¹

theorem finiteNorm_pos : 0<finiteNorm c t hn v hv i := inv_pos.mpr (v.pos (normalizer_ne c t hn v hv i))
theorem original_bounds (n : Fin 2) :
    v (![ContactBicanonicalPointHeight318.a0 c t hn i,ContactBicanonicalPointHeight318.a1 c t hn i] n)*
      finiteNorm c t hn v hv i≤1 :=
  (Classical.choose_spec (exists_normalization c t hn v hv i)).2.2.1 n

/-- The constructed norm is independent of the chosen original integral
chart because the common fiber and exact original section pair fix it. -/
theorem finiteNorm_eq_max_inverse : finiteNorm c t hn v hv i=
    (max (v (ContactBicanonicalPointHeight318.a0 c t hn i))
      (v (ContactBicanonicalPointHeight318.a1 c t hn i)))⁻¹ := by
  rw [finiteNorm,normalizer_max]
end OriginalGoodPlaceCotangentNorms318
