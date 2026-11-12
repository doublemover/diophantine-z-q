module
public import ActualOriginalJointLevelDensity318
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public section
noncomputable section
namespace ActualOriginalNormalProfile318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalNormalLevelChart318
open ActualOriginalJointLevelDensity318 ActualOriginalPositiveGraphIntegral318 MeasureTheory
set_option maxHeartbeats 16000000

@[expose] def normalProfile (κ : ℝ) (W : Coordinates ℝ→ℝ) (s : ℝ) : ℝ :=
  ∫v : Parameters,levelDensity κ W (s,v)

lemma actual_profile_zero (κ : ℝ) (W : Coordinates ℝ→ℝ) :
    normalProfile κ W 0=graphMass κ W := by
  unfold normalProfile graphMass
  exact integral_congr_ae (Filter.Eventually.of_forall (level_density_zero κ W))

lemma compact_marginal_continuous (D : LevelParameters→ℝ)
    (hD : Continuous D) (hDc : HasCompactSupport D) :
    Continuous (fun s : ℝ => ∫v : Parameters,D (s,v)) := by
  have hK : IsCompact (Prod.snd '' tsupport D) := hDc.isCompact.image continuous_snd
  have hzero : ∀s : ℝ,∀v : Parameters,s∈(Set.univ : Set ℝ) →
      v∉Prod.snd '' tsupport D → D (s,v)=0 := by
    intro s v _ hv
    by_contra hh
    exact hv ⟨(s,v),subset_closure hh,rfl⟩
  have hc := continuousOn_integral_of_compact_support (μ:=volume)
    (f:=fun s v => D (s,v)) (s:=Set.univ) hK hD.continuousOn hzero
  exact continuousOn_univ.mp hc

lemma compact_marginal_compact (D : LevelParameters→ℝ) (hDc : HasCompactSupport D) :
    HasCompactSupport (fun s : ℝ => ∫v : Parameters,D (s,v)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hDc.isCompact.image continuous_fst)
  intro s hs
  by_contra hn
  have hz : (fun v : Parameters => D (s,v))=fun _ => 0 := by
    funext v
    by_contra hh
    exact hn ⟨(s,v),subset_closure hh,rfl⟩
  apply hs
  rw [hz]
  simp

/-- The ACTUAL marginal of the original normal-coordinate density is
continuous, compactly supported, nonnegative and integrable. Its zero-level
value is the already integrated original graph mass. -/
theorem actual_profile_properties (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W) (hWn : ∀x,0≤W x)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    Continuous (normalProfile κ W) ∧ HasCompactSupport (normalProfile κ W) ∧
      (∀s,0≤normalProfile κ W s) ∧ Integrable (normalProfile κ W) ∧
      normalProfile κ W 0=graphMass κ W := by
  have hc := level_density_continuous κ η hη W hW hb
  have hk := level_density_compact κ η hη W hWc hb
  have hpc := compact_marginal_continuous (levelDensity κ W) hc hk
  have hpk := compact_marginal_compact (levelDensity κ W) hk
  refine ⟨hpc,hpk,?_,hpc.integrable_of_hasCompactSupport hpk,actual_profile_zero κ W⟩
  intro s
  exact integral_nonneg (fun v => level_density_nonneg κ W hWn (s,v))

end ActualOriginalNormalProfile318
