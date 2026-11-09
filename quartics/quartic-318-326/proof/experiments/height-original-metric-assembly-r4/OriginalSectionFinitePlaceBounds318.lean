module
public import OriginalPointPrimitiveChart318
public section
noncomputable section
namespace OriginalSectionFinitePlaceBounds318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open IntegralEvaluatedPointCharts318 ActualFinitePlaceIntegers318
open ContactBicanonicalPointHeight318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1)

/-- Join the ORIGINAL evaluated J² sections to an actual integral chart of
the SAME original signed-root point. The nonzero scalar is constructed from
the first original section and the first actual chart coefficient; both
section equalities and the exact finite-place norm bound are then proved.
This does not choose an archimedean metric or assert global adelic support. -/
theorem exists_original_bound (i : Fin 4) :
    ∃ (o : Option (Fin 4)) (φ : ChartRing (V c t v) (localTwists c t v hv) o →+* V c t v)
      (α : K c t),
      Spec.map (CommRingCat.ofHom (algebraMap (V c t v) (K c t))) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ embedding (V c t v) (localTwists c t v hv) o=
          IntegralValuativeGenericPoint318.point (V c t v) (K c t) (localTwists c t v hv)
            (t:K c t) (roots c t) (local_root_equations c t v hv) ∧
      α=a0 c t hn i/algebraMap (V c t v) (K c t)
        (φ (coefficient (V c t v) (localTwists c t v hv) o 0)) ∧
      α≠0 ∧
      (∀ n : Fin 2, (![a0 c t hn i,a1 c t hn i] n)=
        α*algebraMap (V c t v) (K c t) (φ (coefficient (V c t v) (localTwists c t v hv) o n))) ∧
      (∀ n : Fin 2, v (![a0 c t hn i,a1 c t hn i] n)*(v α)⁻¹≤1) ∧
      max (v (a0 c t hn i)) (v (a1 c t hn i))=v α := by
  obtain ⟨o,φ,hg,hr,hm⟩ := OriginalPointPrimitiveChart318.exists_primitive_chart c t v hv
  let ψ := (algebraMap (V c t v) (K c t)).comp φ
  let b0 := ψ (coefficient (V c t v) (localTwists c t v hv) o 0)
  let b1 := ψ (coefficient (V c t v) (localTwists c t v hv) o 1)
  have hb : b1=(t:K c t)*b0 := hr
  have hb0 : b0≠0 := by
    intro hz
    have hz1 : b1=0 := by rw [hb,hz,mul_zero]
    change max (v b0) (v b1)=1 at hm
    rw [hz,hz1,map_zero,max_self] at hm
    exact zero_ne_one hm
  let α := a0 c t hn i/b0
  have hα : α≠0 := div_ne_zero (a0_ne c t hn i) hb0
  have h0 : a0 c t hn i=α*b0 := (div_mul_cancel₀ _ hb0).symm
  have h1 : a1 c t hn i=α*b1 := by
    rw [ratio c t hn i,hb,h0]
    ring
  have hp := primitive (V c t v) (localTwists c t v hv)
    (ContactFinitePlaceBaseMap318.separation_unit c v hv) o
  have hnrm := IntegralUnitPairNorm318.normalized_pair_bound ψ v (center_bound v φ)
    (coefficient (V c t v) (localTwists c t v hv) o 0)
    (coefficient (V c t v) (localTwists c t v hv) o 1) hp α hα
  have hmax := IntegralUnitPairNorm318.scaled_pair_max ψ v (center_bound v φ)
    (coefficient (V c t v) (localTwists c t v hv) o 0)
    (coefficient (V c t v) (localTwists c t v hv) o 1) hp α
  refine ⟨o,φ,α,hg,rfl,hα,?_,?_,?_⟩
  · intro n
    fin_cases n
    · exact h0
    · exact h1
  · intro n
    fin_cases n
    · change v (a0 c t hn i)*(v α)⁻¹≤1
      rw [h0]
      exact hnrm.1
    · change v (a1 c t hn i)*(v α)⁻¹≤1
      rw [h1]
      exact hnrm.2
  · rw [h0,h1]
    exact hmax

/-- Any two primitive original chart comparisons give the same finite-place
normalizing factor. No arbitrary per-chart scaling is left in this result. -/
theorem normalization_unique (i : Fin 4) (α β : K c t)
    (hα : max (v (a0 c t hn i)) (v (a1 c t hn i))=v α)
    (hβ : max (v (a0 c t hn i)) (v (a1 c t hn i))=v β) :
    (v α)⁻¹=(v β)⁻¹ := congrArg Inv.inv (hα.symm.trans hβ)
end OriginalSectionFinitePlaceBounds318
