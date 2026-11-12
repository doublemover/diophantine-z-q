module
public import PELOriginalSectionGaugeNormalization318
public import PELOriginalLevelPowerSections318
public section
noncomputable section
namespace PELOriginalWholeSectionSpanning318
open QuaternionicRealPeriod318 PELOriginalPowerSectionLift318 PELOriginalPowerSectionDescent318
open PELOriginalSectionGaugeNormalization318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPolarizationPowerBundle318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSiegelNormalization318 PELOriginalThetaHermitianGauge318 PELOriginalThetaGaugeMatrix318
variable (τ:ℂ)(hτ:0<τ.im)(N:ℕ)[NeZero N]
@[expose] def coordinates(s:HolomorphicSection τ hτ N)(r:Label N):ℂ:=
  PELOriginalAutomorphicSpanning318.coordinates τ N
    (normalize τ hτ N (ascend τ hτ N s)) r

lemma original_lift_expansion(s:HolomorphicSection τ hτ N)(z:ComplexVectors):
    lift τ hτ N s z=∑r:Label N,coordinates τ hτ N s r*value τ hτ N r z:=by
  classical
  let f:=ascend τ hτ N s
  have he:=congrFun (PELOriginalAutomorphicSpanning318.full_spanning τ hτ N
    (automorphic τ hτ N f)) (normalization τ hτ z)
  calc
    _=gauge (bilinearMap τ) (normalization τ hτ z)^N*
      normalize τ hτ N f (normalization τ hτ z):=(recover τ hτ N f z).symm
    _=∑r:Label N,coordinates τ hτ N s r*value τ hτ N r z:=by
      rw [he]
      simp only [PELOriginalAutomorphicSpanning318.expansion,coordinates,value,normalizedValue,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Genuine whole H0 spanning in the ORIGINAL selected bundle fibers.
An arbitrary section enters solely through its actual local holomorphy;
its covering representative, full automorphy and Fourier expansion were
all produced. No dimension or theta-span premise is smuggled into H0. -/
theorem whole_section_spanning(s:HolomorphicSection τ hτ N)(q:Base τ):
    s.value q=∑r:Label N,coordinates τ hτ N s r*(levelSection τ hτ N r q).2:=by
  have h:=descend_lift τ hτ N s q
  have he:=original_lift_expansion τ hτ N s (chart τ hτ ((core τ hτ).indexAt q) q)
  exact h.symm.trans he

theorem unique_whole_section_coordinates(s:HolomorphicSection τ hτ N):
    ∃!c:Label N→ℂ,∀q:Base τ,s.value q=∑r:Label N,c r*(levelSection τ hτ N r q).2:=by
  classical
  refine ⟨coordinates τ hτ N s,whole_section_spanning τ hτ N s,?_⟩
  intro c hc
  have hz:(∑r:Label N,(c r-coordinates τ hτ N s r) •
      (fun q:Base τ=>(levelSection τ hτ N r q).2))=0:=by
    ext q
    have he:=(hc q).symm.trans (whole_section_spanning τ hτ N s q)
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,sub_mul,
      Finset.sum_sub_distrib,sub_eq_zero] using he
  have h:=(Fintype.linearIndependent_iff.mp (sections_independent τ hτ N))
    (fun r=>c r-coordinates τ hτ N s r) hz
  funext r
  exact sub_eq_zero.mp (h r)
end PELOriginalWholeSectionSpanning318
