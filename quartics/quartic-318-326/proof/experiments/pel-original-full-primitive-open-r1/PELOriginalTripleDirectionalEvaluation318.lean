module
public import PELOriginalTripleEvaluation318
public import PELOriginalAllLevelHolomorphicMap318
public section
noncomputable section
namespace PELOriginalTripleDirectionalEvaluation318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPowerSectionLift318 PELOriginalPowerSectionDescent318
open PELOriginalWholeSectionSpanning318
variable (τ:ℂ)(hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ
@[expose] def direction(x v:ComplexVectors):ℂ:=fderiv ℂ F x v
@[expose] def levelDirection(r:Label 3)(x v:ComplexVectors):ℂ:=
  fderiv ℂ (value τ hτ 3 r) x v
lemma level_line(r:Label 3)(x v:ComplexVectors):
    HasDerivAt (fun t:ℂ=>value τ hτ 3 r (x+t • v)) (levelDirection τ hτ r x v) 0:=by
  simpa only [zero_smul,add_zero,one_smul] using
    (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 r x).hasFDerivAt.comp_hasDerivAt 0
      (((hasDerivAt_id (0:ℂ)).smul_const v).const_add x)

/-- A true zero direction of all actual projective ratios forces one
common scalar derivative law on the entire homogeneous coordinate vector. -/
lemma common_slope(x v:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j x≠0)
    (hk:∀r:Label 3,fderiv ℂ (fun z=>value τ hτ 3 r z/value τ hτ 3 j z) x v=0):
    ∀r:Label 3,levelDirection τ hτ r x v=
      (levelDirection τ hτ j x v/value τ hτ 3 j x)*value τ hτ 3 r x:=by
  intro r
  have hq:HasDerivAt (fun t:ℂ=>value τ hτ 3 r (x+t • v)/value τ hτ 3 j (x+t • v))
      ((levelDirection τ hτ r x v*value τ hτ 3 j x-
        value τ hτ 3 r x*levelDirection τ hτ j x v)/(value τ hτ 3 j x)^2) 0:=by
    simpa only [zero_smul,add_zero] using
      (level_line τ hτ r x v).div (level_line τ hτ j x v)
        (by simpa only [zero_smul,add_zero] using hj)
  have hd:DifferentiableAt ℂ (fun z=>value τ hτ 3 r z/value τ hτ 3 j z) x:=
    (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 r x).div
      (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j x) hj
  have hz:HasDerivAt (fun t:ℂ=>value τ hτ 3 r (x+t • v)/value τ hτ 3 j (x+t • v)) 0 0:=by
    simpa only [zero_smul,add_zero,one_smul,hk r] using
      hd.hasFDerivAt.comp_hasDerivAt 0 (((hasDerivAt_id (0:ℂ)).smul_const v).const_add x)
  have he:=hq.unique hz
  have hn:= (div_eq_zero_iff).mp he
  have hp:levelDirection τ hτ r x v*value τ hτ 3 j x-
      value τ hτ 3 r x*levelDirection τ hτ j x v=0:=
    hn.resolve_right (pow_ne_zero 2 hj)
  field_simp [hj]
  linear_combination hp

/-- Whole H0 spanning propagates the SAME derivative scalar to every
actual original cube-line section, not merely the nine basis functions. -/
lemma whole_section_line(x v:ComplexVectors)(c:ℂ)
    (hc:∀r:Label 3,levelDirection τ hτ r x v=c*value τ hτ 3 r x)
    (s:HolomorphicSection τ hτ 3):
    HasDerivAt (fun t:ℂ=>lift τ hτ 3 s (x+t • v)) (c*lift τ hτ 3 s x) 0:=by
  have he: (fun t:ℂ=>lift τ hτ 3 s (x+t • v))=
      (fun t:ℂ=>∑r:Label 3,coordinates τ hτ 3 s r*value τ hτ 3 r (x+t • v)):=by
    funext t
    exact original_lift_expansion τ hτ 3 s _
  rw [he,original_lift_expansion,Finset.mul_sum]
  have hd:=HasDerivAt.fun_sum (u:=Finset.univ)
    (fun r _=>(level_line τ hτ r x v).const_mul (coordinates τ hτ 3 s r))
  convert hd using 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [hc r]
  ring
lemma original_line(x v a:ComplexVectors):
    HasDerivAt (fun t:ℂ=>F (x+t • v+a)) (direction τ hτ (x+a) v) 0:=by
  have h:= (PELOriginalGaugedTheta318.holomorphic τ hτ (x+a)).hasFDerivAt.comp_hasDerivAt 0
    ((((hasDerivAt_id (0:ℂ)).smul_const v).const_add x).add_const a)
  simpa only [zero_smul,add_zero,one_smul] using h

/-- The differentiated balanced-triple identity holds for ALL shifts,
including every zero of the actual theta. No logarithmic ratio is used
in extracting this identity from genuine sections. -/
theorem triple_directional(x v:ComplexVectors)(c:ℂ)
    (hc:∀r:Label 3,levelDirection τ hτ r x v=c*value τ hτ 3 r x):
    ∀a b:ComplexVectors,
      direction τ hτ (x+a) v*F (x+b)*F (x+(-a-b))+
      F (x+a)*direction τ hτ (x+b) v*F (x+(-a-b))+
      F (x+a)*F (x+b)*direction τ hτ (x+(-a-b)) v=
        c*(F (x+a)*F (x+b)*F (x+(-a-b))):=by
  intro a b
  have hs:=whole_section_line τ hτ x v c hc
    (descend τ hτ 3 (PELOriginalTripleEvaluation318.tripleFunction τ hτ a b))
  simp only [lift_descend,PELOriginalTripleEvaluation318.triple_formula] at hs
  have hp:=((original_line τ hτ x v a).mul (original_line τ hτ x v b)).mul
    (original_line τ hτ x v (-a-b))
  have he:=hp.unique hs
  linear_combination he
end PELOriginalTripleDirectionalEvaluation318
