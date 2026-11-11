module
public import PELOriginalWholeHZeroDimension318
public import PELOriginalHigherPowerGeneration318
public section
noncomputable section
namespace PELOriginalFiniteThetaGeneration318
open QuaternionicRealPeriod318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationPowerBundle318 PELOriginalPowerSectionLift318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalWholeSectionSpanning318
variable (τ:ℂ)(hτ:0<τ.im)

/-- The previously produced balanced products are elements of the SAME
whole original H0 whose complete characteristic expansion is now proved. -/
@[expose] def balancedSection(n:ℕ)(a:ComplexVectors):HolomorphicSection τ hτ (n+2) where
  value q:=(PELOriginalHigherPowerGeneration318.higherSection τ hτ n a q).2
  holomorphic c:=PELOriginalHigherPowerGeneration318.holomorphic_in_original_charts τ hτ n a c

/-- Every positive level at least TWO has a concrete finite N²-family
with no common zero on the actual original surface. Infinite translated
products are only used as produced test sections; whole H0 spanning
forces a nonzero member of the fixed finite characteristic family. -/
theorem finite_basepoint_free(n:ℕ)(q:Base τ):
    ∃r:Label (n+2),(levelSection τ hτ (n+2) r q).2≠0:=by
  classical
  obtain ⟨a,ha⟩:=PELOriginalHigherPowerGeneration318.all_powers_basepoint_free τ hτ n q
  by_contra h
  push_neg at h
  have he:=whole_section_spanning τ hτ (n+2) (balancedSection τ hτ n a) q
  have hz:(PELOriginalHigherPowerGeneration318.higherSection τ hτ n a q).2=0:=by
    simpa only [balancedSection,h,mul_zero,Finset.sum_const_zero] using he
  exact ha hz

theorem finite_evaluation_surjective(n:ℕ)(q:Base τ)(v:PowerFiber τ hτ (n+2) q):
    ∃c:Label (n+2)→ℂ,∑r:Label (n+2),c r*(levelSection τ hτ (n+2) r q).2=v:=by
  classical
  obtain ⟨r,hr⟩:=finite_basepoint_free τ hτ n q
  refine ⟨fun k=>if k=r then v/(levelSection τ hτ (n+2) r q).2 else 0,?_⟩
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true]
  exact div_mul_cancel₀ v hr

/-- The corresponding actual homogeneous coordinate vector never
vanishes. This is generation only, NOT point/tangent separation. -/
theorem homogeneous_vector_nonzero(n:ℕ)(q:Base τ):
    (fun r:Label (n+2)=>(levelSection τ hτ (n+2) r q).2)≠0:=by
  obtain ⟨r,hr⟩:=finite_basepoint_free τ hτ n q
  intro h
  exact hr (congrFun h r)
end PELOriginalFiniteThetaGeneration318
