module
public import FiniteFlatPrincipalBasis318
public import FifthChartNorm318
public import FiniteFlatGenericRank318
public section
noncomputable section
namespace FifthPushforwardModules318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
local instance chartNonempty (b:Bool):Nonempty (chartOpen b):=chart_nonempty b
local instance preimageNonempty (b:Bool):Nonempty (map⁻¹ᵁchartOpen b):=
  DominantFunctionField318.preimage_nonempty map (chartOpen b)
abbrev R (b:Bool):=Γ(Target,chartOpen b)
abbrev S (b:Bool):=Γ(Model,map⁻¹ᵁchartOpen b)
@[expose,instance_reducible] def sectionAlgebra (b:Bool):Algebra (R b) (S b):=
  (map.app (chartOpen b)).hom.toAlgebra
attribute [local instance] sectionAlgebra
lemma target_dedekind (b:Bool):IsDedekindDomain (R b):=by
  cases b
  · letI:=CompletedRationalDedekind318.affine A B discriminant_unit
    exact DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (ShortAffineJacobian318.Ring A B)) (WeierstrassGluing318.finiteChart A B)
  · letI:=CompletedRationalDedekind318.infinity A B discriminant_unit
    exact DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (InfinityChart318.Ring A B)) (WeierstrassGluing318.infinityChart A B)
lemma finite (b:Bool):Module.Finite (R b) (S b):=map.finite_app (chartOpen b) (chart_affine b)
lemma flat (b:Bool):Module.Flat (R b) (S b):=by
  letI:=target_dedekind b
  exact DedekindAffineFlat318.app_flat map (chartOpen b)
lemma finitePresentation (b:Bool):Module.FinitePresentation (R b) (S b):=by
  letI:=target_dedekind b
  letI:=finite b
  exact Module.finitePresentation_of_finite (R b) (S b)
/-- Actual section-module rank at every prime of either complete target chart. -/
lemma rank_eight (b:Bool) (p:PrimeSpectrum (R b)):
    Module.rankAtStalk (S b) p=8:=by
  letI:=finite b
  letI:=flat b
  letI:Algebra Target.functionField Model.functionField:=AffineDominantNorm318.fieldAlgebra map
  letI:Algebra (R b) Model.functionField:=
    ((algebraMap Target.functionField Model.functionField).comp
      (algebraMap (R b) Target.functionField)).toAlgebra
  letI:IsScalarTower (R b) Target.functionField Model.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower (R b) (S b) Model.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:R b⟶Model.functionField=>g a)
      (DominantFunctionField318.map_germ map (chartOpen b)))
  letI:IsFractionRing (R b) Target.functionField:=
    functionField_isFractionRing_of_isAffineOpen Target (chartOpen b) (chart_affine b)
  letI:IsFractionRing (S b) Model.functionField:=
    functionField_isFractionRing_of_isAffineOpen Model (map⁻¹ᵁchartOpen b) ((chart_affine b).preimage map)
  have h:=FiniteFlatGenericRank318.affine_rank_eq_fraction_degree
    (R b) (S b) Target.functionField Model.functionField p
  rw [Scheme.Hom.finrank_SpecMap_algebraMap] at h
  exact h.trans FifthCompletedDegree318.actual_generic_degree_eight
/-- The original finite-flat pushforward has an actual rank-eight basis
after a principal localization containing each specified prime. -/
lemma exists_principal_basis (b:Bool) (p:PrimeSpectrum (R b)):
    ∃r:R b,r∉p.asIdeal ∧ Nonempty
      (Module.Basis (Fin 8) (Localization.Away r) (LocalizedModule.Away r (S b))):=by
  letI:=finitePresentation b
  letI:=flat b
  exact FiniteFlatPrincipalBasis318.exists_basis_of_rank (R b) (S b) p 8 (rank_eight b p)
end FifthPushforwardModules318
