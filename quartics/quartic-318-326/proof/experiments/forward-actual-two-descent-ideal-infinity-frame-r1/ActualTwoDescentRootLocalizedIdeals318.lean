module
public import ActualTwoDescentRootPrincipalOpenCover318
public section
noncomputable section
namespace ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootCofactorData318 ActualTwoDescentRootPrincipalOpenCover318
variable {K : Type*} [Field K] [CharZero K]

def localizedRootIdeal (n : K) (i : Fin 3) (b : Bool) : Ideal (RootChartRing n i b) :=
  Ideal.map (rootChartMap n i b) (rootIdeal n i)
lemma actual_localized_root_generators (n : K) (i : Fin 3) (b : Bool) :
    localizedRootIdeal n i b=Ideal.span
      {rootChartMap n i b (rootNumerator n i),rootChartMap n i b (affineY n)} := by
  rw [localizedRootIdeal,actual_root_ideal_generators,Ideal.map_span,Set.image_pair]

lemma actual_root_complement_unit_ideal (n : K) (i : Fin 3) :
    localizedRootIdeal n i false=⊤ := by
  apply Ideal.eq_top_iff_one.mpr
  have hf : rootChartMap n i false (rootNumerator n i)∈localizedRootIdeal n i false := by
    rw [actual_localized_root_generators]
    exact Ideal.subset_span (by simp)
  have h := (localizedRootIdeal n i false).mul_mem_right (rootChartInverse n i false) hf
  change rootChartMap n i false (rootChartElement n i false)*rootChartInverse n i false∈_ at h
  simpa only [actual_root_chart_inverse] using h

lemma actual_root_local_equation (n : K) (i : Fin 3) (b : Bool) :
    (rootChartMap n i b (affineY n))^2=
      rootChartMap n i b (rootNumerator n i)*rootChartMap n i b (rootCofactor n i) := by
  simpa only [map_pow,map_mul] using congrArg (rootChartMap n i b) (actual_root_factorization n i)
lemma actual_root_branch_division (n : K) (i : Fin 3) :
    rootChartMap n i true (rootNumerator n i)=
      (rootChartMap n i true (affineY n))^2*rootChartInverse n i true := by
  rw [actual_root_local_equation,mul_assoc]
  change _=_*(rootChartMap n i true (rootChartElement n i true)*rootChartInverse n i true)
  rw [actual_root_chart_inverse,mul_one]

/-- On the actual root-containing open, y is a genuine module generator;
the equality is of literal extended ideals, not only ideal classes. -/
theorem actual_root_branch_principal (n : K) (i : Fin 3) :
    localizedRootIdeal n i true=Ideal.span {rootChartMap n i true (affineY n)} := by
  rw [actual_localized_root_generators]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl|ha
    · rw [actual_root_branch_division,Ideal.mem_span_singleton]
      refine ⟨rootChartMap n i true (affineY n)*rootChartInverse n i true,?_⟩
      ring
    · exact Ideal.subset_span ha
  · apply Ideal.span_mono
    intro a ha
    exact Set.mem_insert_of_mem _ ha
end ActualTwoDescentRootLocalizedIdeals318
