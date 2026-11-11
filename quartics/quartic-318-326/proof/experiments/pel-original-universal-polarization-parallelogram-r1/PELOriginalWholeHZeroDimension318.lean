module
public import PELOriginalWholeSectionSpanning318
public section
noncomputable section
namespace PELOriginalWholeHZeroDimension318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPowerSectionLift318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPolarizationPowerBundle318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalWholeSectionSpanning318
variable (τ:ℂ)(hτ:0<τ.im)(N:ℕ)[NeZero N]
abbrev SectionValues:=∀q:Base τ,PowerFiber τ hτ N q
@[expose] def localCoefficient(a:ComplexVectors)(s:SectionValues τ hτ N)(z:ComplexVectors):ℂ:=
  ((powerCore τ hτ N).localTriv a ⟨projection (P τ) z,s (projection (P τ) z)⟩).2
lemma coefficient_formula(a:ComplexVectors)(s:SectionValues τ hτ N)(z:ComplexVectors):
    localCoefficient τ hτ N a s z=
      transition τ hτ ((core τ hτ).indexAt (projection (P τ) z)) a
        (projection (P τ) z)^N*s (projection (P τ) z):=rfl
lemma coefficient_zero(a:ComplexVectors):localCoefficient τ hτ N a 0=0:=by
  funext z;rw [coefficient_formula];simp
lemma coefficient_add(a:ComplexVectors)(s t:SectionValues τ hτ N):
    localCoefficient τ hτ N a (s+t)=localCoefficient τ hτ N a s+localCoefficient τ hτ N a t:=by
  funext z;simp only [coefficient_formula,Pi.add_apply,mul_add]
lemma coefficient_smul(a:ComplexVectors)(c:ℂ)(s:SectionValues τ hτ N):
    localCoefficient τ hτ N a (c • s)=c • localCoefficient τ hτ N a s:=by
  funext z;simp only [coefficient_formula,Pi.smul_apply,smul_eq_mul];ring

/-- The ACTUAL whole vector space of holomorphic sections of the
original power cocycle: membership is local holomorphy in its genuine
bundle charts, with no theta span or finite-dimensionality premise. -/
@[expose] def HZero:Submodule ℂ (SectionValues τ hτ N) where
  carrier:={s|∀a:ComplexVectors,DifferentiableOn ℂ (localCoefficient τ hτ N a s)
    (chart τ hτ a).target}
  zero_mem':=by intro a;rw [coefficient_zero];exact differentiableOn_const 0
  add_mem':=by intro s t hs ht a;rw [coefficient_add];exact (hs a).add (ht a)
  smul_mem':=by intro c s hs a;rw [coefficient_smul];exact (hs a).const_smul c
@[expose] def asSection(s:HZero τ hτ N):HolomorphicSection τ hτ N:=⟨s.val,s.property⟩
@[expose] def thetaVector(r:Label N):HZero τ hτ N:=
  ⟨fun q=>(levelSection τ hτ N r q).2,holomorphic_in_original_charts τ hτ N r⟩

@[expose] def expansionMap:(Label N→ℂ)→ₗ[ℂ]HZero τ hτ N where
  toFun c:=∑r:Label N,c r • thetaVector τ hτ N r
  map_add' c d:=by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c d:=by simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]
lemma expansionMap_value(c:Label N→ℂ)(q:Base τ):
    (expansionMap τ hτ N c).val q=∑r:Label N,c r*(levelSection τ hτ N r q).2:=by
  simp only [expansionMap,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
    Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,thetaVector]
lemma expansionMap_injective:Function.Injective (expansionMap τ hτ N):=by
  intro c d h
  have hz:(∑r:Label N,(c r-d r) • (fun q:Base τ=>(levelSection τ hτ N r q).2))=0:=by
    funext q
    have he:=congrArg (fun s:HZero τ hτ N=>s.val q) h
    simp only [expansionMap_value] at he
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,sub_mul,
      Finset.sum_sub_distrib,sub_eq_zero] using he
  have he:=(Fintype.linearIndependent_iff.mp (sections_independent τ hτ N))
    (fun r=>c r-d r) hz
  funext r;exact sub_eq_zero.mp (he r)
lemma expansionMap_surjective:Function.Surjective (expansionMap τ hτ N):=by
  intro s
  refine ⟨coordinates τ hτ N (asSection τ hτ N s),?_⟩
  apply Subtype.ext
  funext q
  exact (expansionMap_value τ hτ N _ q).trans
    (whole_section_spanning τ hτ N (asSection τ hτ N s) q).symm

/-- Actual full H0, not merely a selected theta subspace, is linearly
equivalent to its N² explicitly indexed coefficient vector. -/
@[expose] def coefficientEquivalence:(Label N→ℂ)≃ₗ[ℂ]HZero τ hτ N:=
  LinearEquiv.ofBijective (expansionMap τ hτ N)
    ⟨expansionMap_injective τ hτ N,expansionMap_surjective τ hτ N⟩
instance finiteDimensional:FiniteDimensional ℂ (HZero τ hτ N):=
  FiniteDimensional.of_surjective (expansionMap τ hτ N) (expansionMap_surjective τ hτ N)
theorem actual_hzero_dimension:Module.finrank ℂ (HZero τ hτ N)=N^2:=by
  rw [←(coefficientEquivalence τ hτ N).finrank_eq]
  simp [Module.finrank_pi,Label,Fintype.card_prod,pow_two]
end PELOriginalWholeHZeroDimension318
