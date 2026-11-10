module
public import OriginalExcludedPlaceData318
public section
noncomputable section
namespace OriginalFiniteNormAssembly318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open OriginalExcludedPlaceData318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (B : ExcludedGenerators c t hn i)

/-- The finite norm uses the CONSTRUCTED original cotangent lattice at every
good place, and only the explicit residual finite-place data elsewhere. -/
@[expose] def finiteNorm (v : FinitePlace (K c t)) : ℝ :=
  if hv : v (denominator c:K c t)=1 then OriginalGoodPlaceCotangentNorms318.finiteNorm c t hn v hv i
  else excludedNorm c t hn i B ⟨v,hv⟩

theorem finiteNorm_good (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1) :
    finiteNorm c t hn i B v=OriginalGoodPlaceCotangentNorms318.finiteNorm c t hn v hv i :=
  dif_pos hv

theorem finiteNorm_pos (v : FinitePlace (K c t)) : 0<finiteNorm c t hn i B v := by
  unfold finiteNorm
  split_ifs with hv
  · exact OriginalGoodPlaceCotangentNorms318.finiteNorm_pos c t hn v hv i
  · exact excludedNorm_pos c t hn i B ⟨v,hv⟩

theorem original_bound (v : FinitePlace (K c t)) (n : Fin 2) :
    v (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*finiteNorm c t hn i B v≤1 := by
  unfold finiteNorm
  split_ifs with hv
  · exact OriginalGoodPlaceCotangentNorms318.original_bounds c t hn v hv i n
  · exact excluded_bound c t hn i B ⟨v,hv⟩ n

/-- Global finite support is DERIVED from the actual good-place family and
the explicit finite excluded set. No support hypothesis is required for B. -/
theorem finite_support : Function.HasFiniteMulSupport (finiteNorm c t hn i B) := by
  obtain ⟨S,hS,hgood⟩ := OriginalGoodNormSupport318.finite_support c t hn i
  have hbad := ContactFinitePlaceBaseMap318.excluded_places_finite (K:=K c t) c
  apply (hS.union hbad).subset
  intro v hv
  change finiteNorm c t hn i B v≠1 at hv
  by_contra h
  have hgoodv : v (denominator c:K c t)=1 := by
    by_contra hb
    exact h (Or.inr hb)
  have hS' : v∉S := fun hs => h (Or.inl hs)
  exact hv ((finiteNorm_good c t hn i B v hgoodv).trans (hgood v hgoodv hS'))
end OriginalFiniteNormAssembly318
