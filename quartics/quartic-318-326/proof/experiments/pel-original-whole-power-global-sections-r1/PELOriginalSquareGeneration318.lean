module
public import PELOriginalPolarizationPowerBundle318
public import PELOriginalNonzeroThetaSection318
public import EntireSimultaneousNonzero318
public section
noncomputable section
namespace PELOriginalSquareGeneration318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalBalancedThetaProducts318
open PELOriginalPolarizationAutomorphy318
variable (τ:ℂ) (hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

/-- Actual simultaneous avoidance for the two opposite translates of
our produced original theta. No generic-point or zero-locus hypothesis. -/
theorem exists_pair_nonzero (z:ComplexVectors):
    ∃a,F (z+a)*F (z-a)≠0:=by
  obtain ⟨p,hp⟩:=PELOriginalNonzeroThetaSection318.exists_original_value_nonzero τ hτ
  have hf:Differentiable ℂ (fun a:ComplexVectors=>F (z+a)):=
    (PELOriginalGaugedTheta318.holomorphic τ hτ).comp (differentiable_const.add differentiable_id)
  have hg:Differentiable ℂ (fun a:ComplexVectors=>F (z-a)):=
    (PELOriginalGaugedTheta318.holomorphic τ hτ).comp (differentiable_const.sub differentiable_id)
  apply EntireSimultaneousNonzero318.differentiable_exists_product_ne_zero
    (fun a=>F (z+a)) (fun a=>F (z-a))
    hf hg
  · refine ⟨p-z,?_⟩
    rw [show z+(p-z)=p by abel]
    exact hp
  · refine ⟨z-p,?_⟩
    simpa only [sub_sub_cancel] using hp

/-- A family of actual global sections of the square of the original
line cocycle. Opposite translations cancel their otherwise nontrivial
flat factors, so every member belongs to this ONE fixed power bundle. -/
@[expose] def squareSection (a:ComplexVectors) (q:Base τ):PowerTotal τ hτ 2:=
  powerSection τ hτ 2 (product τ hτ 2 (pair a)) q
lemma continuous (a:ComplexVectors):Continuous (squareSection τ hτ a):=
  continuous_section τ hτ 2 _ (product_holomorphic τ hτ 2 (pair a)).continuous
    (original_automorphy τ hτ 2 (pair a) (pair_balanced a))
lemma holomorphic_in_original_charts (a c:ComplexVectors):
    DifferentiableOn ℂ (fun z:ComplexVectors=>((powerCore τ hτ 2).localTriv c
      (squareSection τ hτ a (projection (P τ) z))).2) (chart τ hτ c).target:=
  holomorphic_section τ hτ 2 _ (product_holomorphic τ hτ 2 (pair a))
    (original_automorphy τ hτ 2 (pair a) (pair_balanced a)) c

/-- Basepoint-free at EVERY actual original quotient point. The chosen
translate is produced from genuine theta nontriviality and the identity
principle, not supplied as a hidden generation assumption. -/
theorem basepoint_free (q:Base τ):∃a,(squareSection τ hτ a q).2≠0:=by
  let z:ComplexVectors:=chart τ hτ ((core τ hτ).indexAt q) q
  obtain ⟨a,ha⟩:=exists_pair_nonzero τ hτ z
  refine ⟨a,?_⟩
  change product τ hτ 2 (pair a) z≠0
  rw [pair_value]
  exact ha

/-- Rank-one evaluation is genuinely onto: a nonzero member can be
scaled to any vector in the actual selected fiber gauge. -/
theorem evaluation_surjective (q:Base τ) (v:PowerFiber τ hτ 2 q):
    ∃a:ComplexVectors,∃c:ℂ,c*(squareSection τ hτ a q).2=v:=by
  obtain ⟨a,ha⟩:=basepoint_free τ hτ q
  exact ⟨a,v/(squareSection τ hτ a q).2,div_mul_cancel₀ v ha⟩
end PELOriginalSquareGeneration318
