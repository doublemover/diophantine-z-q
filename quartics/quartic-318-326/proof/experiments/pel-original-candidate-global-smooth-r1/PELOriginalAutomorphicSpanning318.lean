module
public import PELOriginalAutomorphicSubspace318
public import EntirePeriodicFourierUniqueness318
public section
noncomputable section
namespace PELOriginalAutomorphicSpanning318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaRealTorus318
open PELOriginalLevelTheta318 PELOriginalLevelThetaIndependence318
open PELOriginalAutomorphicFourierRecurrence318 PELOriginalAutomorphicSubspace318
open EntireDoubleFourierTranslation318 EntireIntegerPeriodicRealTorus318
open ActualDoubleFourierCoefficient318
variable (τ:ℂ) (hτ:0<τ.im) (N:ℕ) [NeZero N]
@[expose] def coordinates(f:ComplexVectors→ℂ)(r:Label N):ℂ:=
  coefficient f (representative N r)/leading τ N r
@[expose] def expansion(f:ComplexVectors→ℂ)(z:ComplexVectors):ℂ:=
  ∑r:Label N,coordinates τ N f r*levelTheta τ N r z
lemma expansion_automorphic(f:ComplexVectors→ℂ):Automorphic τ N (expansion τ N f):=by
  classical
  apply finite_sum τ N Finset.univ (fun r=>coordinates τ N f r • levelTheta τ N r)
  intro r hr
  exact smul_automorphic τ N _ (characteristic_automorphic τ N hτ r)
lemma residual_automorphic {f:ComplexVectors→ℂ}(hf:Automorphic τ N f):
    Automorphic τ N (f-expansion τ N f):=
  sub_automorphic τ N hf (expansion_automorphic τ hτ N f)

lemma residual_torus {f:ComplexVectors→ℂ}(hf:Automorphic τ N f):
    torus (f-expansion τ N f) (residual_automorphic τ hτ N hf).entire.continuous
      (first_period τ N (residual_automorphic τ hτ N hf))
      (second_period τ N (residual_automorphic τ hτ N hf))=
    torus f hf.entire.continuous (first_period τ N hf) (second_period τ N hf)-
      ∑r:Label N,coordinates τ N f r • PELOriginalLevelThetaFourier318.torusTheta τ N r:=by
  classical
  ext q
  obtain ⟨x,rfl⟩:=torusPoint_surjective q
  simp only [ContinuousMap.sub_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    EntireIntegerPeriodicRealTorus318.real_evaluation,Pi.sub_apply,expansion,
    PELOriginalLevelThetaFourier318.real_evaluation τ hτ N,smul_eq_mul]

lemma residual_representatives {f:ComplexVectors→ℂ}(hf:Automorphic τ N f):
    ∀r:Label N,coefficient (f-expansion τ N f) (representative N r)=0:=by
  classical
  intro r
  let g:=f-expansion τ N f
  have hg:=residual_automorphic τ hτ N hf
  rw [←functional_coefficient g hg.entire.continuous
    (first_period τ N hg) (second_period τ N hg) (representative N r)]
  rw [residual_torus τ hτ N hf,map_sub,map_sum]
  simp only [map_smul,PELOriginalLevelThetaFourier318.fourier_exact τ hτ N,
    coefficient_representative]
  rw [functional_coefficient]
  simp [smul_eq_mul,coordinates,leading_nonzero]

/-- EVERY entire function with the full original normalized level-N
lattice rule lies in the span of the N² literal characteristic thetas.
Actual Fourier descent, contour shift, recurrence and uniqueness are all
constructed; neither a dimension bound nor spanning premise is used. -/
theorem full_spanning {f:ComplexVectors→ℂ}(hf:Automorphic τ N f):
    f=expansion τ N f:=by
  have hg:=residual_automorphic τ hτ N hf
  have hc:=coefficients_zero_of_representatives τ N hg (residual_representatives τ hτ N hf)
  have hz:=EntirePeriodicFourierUniqueness318.zero_of_coefficients
    (f-expansion τ N f) hg.entire (first_period τ N hg) (second_period τ N hg) hc
  exact sub_eq_zero.mp hz

/-- The decomposition is unique by the independently proved actual
Fourier independence. This is full-space spanning, not only a statement
about the previously constructed theta subspace. -/
theorem unique_coordinates {f:ComplexVectors→ℂ}(hf:Automorphic τ N f):
    ∃!c:Label N→ℂ,f=fun z=>∑r:Label N,c r*levelTheta τ N r z:=by
  classical
  refine ⟨coordinates τ N f,full_spanning τ hτ N hf,?_⟩
  intro c hc
  have hz:(∑r:Label N,(c r-coordinates τ N f r) • levelTheta τ N r)=0:=by
    ext z
    have he:=congrFun (hc.symm.trans (full_spanning τ hτ N hf)) z
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,sub_mul,
      Finset.sum_sub_distrib,expansion,sub_eq_zero] using he
  have hh:=(Fintype.linearIndependent_iff.mp (entire_independent τ hτ N))
    (fun r=>c r-coordinates τ N f r) hz
  funext r
  exact sub_eq_zero.mp (hh r)
end PELOriginalAutomorphicSpanning318
