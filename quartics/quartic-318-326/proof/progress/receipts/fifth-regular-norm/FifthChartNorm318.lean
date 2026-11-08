module
public import FifthCompletedRank318
public import FifthGenericNorm318
public import AffineDominantNorm318
public section
noncomputable section
namespace FifthChartNorm318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318
set_option maxHeartbeats 450000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Model:=ContactGlobalSmooth318.Model units
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
local instance finiteDomain:IsDomain (ShortAffineJacobian318.Ring A B):=AffineCoordinateDomain318.affine_domain A B
local instance infinityDomain:IsDomain (InfinityChart318.Ring A B):=InfinityCoordinateDomain318.infinity_domain A B
local instance finiteAffine:IsAffine (ShortAffineScheme318.scheme A B):=by
  change IsAffine (Spec (CommRingCat.of (ShortAffineJacobian318.Ring A B)))
  infer_instance
@[expose] def chartOpen:Bool→Target.Opens
  | false=>(WeierstrassGluing318.finiteChart A B).opensRange
  | true=>(WeierstrassGluing318.infinityChart A B).opensRange
lemma chart_affine (b:Bool):IsAffineOpen (chartOpen b):=by
  cases b
  · exact isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B)
  · exact isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B)
lemma chart_nonempty (b:Bool):Nonempty (chartOpen b):=by
  cases b
  · obtain ⟨x⟩:Nonempty (Spec (CommRingCat.of (ShortAffineJacobian318.Ring A B))):=inferInstance
    exact ⟨⟨WeierstrassGluing318.finiteChart A B x,⟨x,rfl⟩⟩⟩
  · obtain ⟨x⟩:Nonempty (Spec (CommRingCat.of (InfinityChart318.Ring A B))):=inferInstance
    exact ⟨⟨WeierstrassGluing318.infinityChart A B x,⟨x,rfl⟩⟩⟩
local instance chartNonempty (b:Bool):Nonempty (chartOpen b):=chart_nonempty b
lemma chart_normal (b:Bool):IsIntegrallyClosed Γ(Target,chartOpen b):=by
  cases b
  · letI:=CompletedRationalDedekind318.affine A B discriminant_unit
    letI:=DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (ShortAffineJacobian318.Ring A B)) (WeierstrassGluing318.finiteChart A B)
    change IsIntegrallyClosed Γ(Target,(WeierstrassGluing318.finiteChart A B).opensRange)
    infer_instance
  · letI:=CompletedRationalDedekind318.infinity A B discriminant_unit
    letI:=DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (InfinityChart318.Ring A B)) (WeierstrassGluing318.infinityChart A B)
    change IsIntegrallyClosed Γ(Target,(WeierstrassGluing318.infinityChart A B).opensRange)
    infer_instance
local instance chartNormal (b:Bool):IsIntegrallyClosed Γ(Target,chartOpen b):=chart_normal b
local instance preimageNonempty (b:Bool):Nonempty (map⁻¹ᵁchartOpen b):=
  DominantFunctionField318.preimage_nonempty map (chartOpen b)
/-- Actual norm on both complete target chart section rings, including all
finite branch values and the chosen elliptic zero. -/
@[expose] def norm (b:Bool):Γ(Model,map⁻¹ᵁchartOpen b)→*Γ(Target,chartOpen b):=
  AffineDominantNorm318.norm map (chartOpen b) (chart_affine b)
lemma original_generic_norm (b:Bool) (s:Γ(Model,map⁻¹ᵁchartOpen b)):
    Target.germToFunctionField (chartOpen b) (norm b s)=
      FifthGenericNorm318.norm (Model.germToFunctionField (map⁻¹ᵁchartOpen b) s):=
  AffineDominantNorm318.embedding map (chartOpen b) (chart_affine b) s
lemma norm_pullback (b:Bool) (s:Γ(Target,chartOpen b)):
    norm b (map.app (chartOpen b) s)=s^8:=by
  change AffineDominantNorm318.norm map (chartOpen b) (chart_affine b)
    (map.app (chartOpen b) s)=s^8
  have h:=AffineDominantNorm318.pullback map (chartOpen b) (chart_affine b) s
  simpa only [FifthCompletedDegree318.actual_generic_degree_eight] using h
lemma norm_unit (b:Bool) {s:Γ(Model,map⁻¹ᵁchartOpen b)} (hs:IsUnit s):IsUnit (norm b s):=
  hs.map (norm b)
end FifthChartNorm318
