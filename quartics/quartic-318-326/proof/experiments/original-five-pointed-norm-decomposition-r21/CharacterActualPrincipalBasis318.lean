module
public import FifthActualLocalDualNorm318
public import CompletedCharacterRank318
public section
noncomputable section
namespace CharacterActualPrincipalBasis318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterTraceBasis318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral : IsIntegral Model := ContactProjectiveModel318.model_integral units
local instance targetIntegral (i : Fin 4) : IsIntegral (Target i) :=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapFinite (i : Fin 4) : IsFinite (completedMap i) := CompletedCharacterFinite318.completedMap_finite i
local instance mapDominant (i : Fin 4) : IsDominant (completedMap i) := CompletedCharacterProper318.completedMap_dominant i
abbrev R (i : Fin 4) (b : Bool) := Γ(Target i,chartOpen i b)
abbrev S (i : Fin 4) (b : Bool) := Γ(Model,completedMap i ⁻¹ᵁ chartOpen i b)
local instance sectionAlgebra (i : Fin 4) (U : (Target i).Opens) : Algebra Γ(Target i,U) Γ(Model,completedMap i ⁻¹ᵁ U) :=
  ((completedMap i).app U).hom.toAlgebra
lemma target_dedekind (i : Fin 4) (b : Bool) : IsDedekindDomain (R i b) := by
  cases b
  · letI := CompletedRationalDedekind318.affine (publishedA i) (publishedB i) (discriminant_unit i)
    exact DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (ShortAffineJacobian318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
  · letI := CompletedRationalDedekind318.infinity (publishedA i) (publishedB i) (discriminant_unit i)
    exact DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (InfinityChart318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i))
variable (i : Fin 4) (b : Bool) [Nonempty (chartOpen i b)]
local instance preimageNonempty : Nonempty (completedMap i ⁻¹ᵁ chartOpen i b) :=
  DominantFunctionField318.preimage_nonempty (completedMap i) (chartOpen i b)
lemma finite : Module.Finite (R i b) (S i b) := (completedMap i).finite_app _ (chart_affine i b)
lemma flat : Module.Flat (R i b) (S i b) := by
  letI := target_dedekind i b
  exact DedekindAffineFlat318.app_flat (completedMap i) (chartOpen i b)
lemma finitePresentation : Module.FinitePresentation (R i b) (S i b) := by
  letI := target_dedekind i b
  letI := finite i b
  exact Module.finitePresentation_of_finite (R i b) (S i b)
lemma rank_eight (p : PrimeSpectrum (R i b)) : Module.rankAtStalk (S i b) p = 8 := by
  letI := finite i b
  letI := flat i b
  letI : Algebra (Target i).functionField Model.functionField := AffineDominantNorm318.fieldAlgebra (completedMap i)
  letI : Algebra (R i b) Model.functionField :=
    ((algebraMap (Target i).functionField Model.functionField).comp
      (algebraMap (R i b) (Target i).functionField)).toAlgebra
  letI : IsScalarTower (R i b) (Target i).functionField Model.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower (R i b) (S i b) Model.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => congrArg (fun g : R i b ⟶ Model.functionField => g a)
      (DominantFunctionField318.map_germ (completedMap i) (chartOpen i b)))
  letI : IsFractionRing (R i b) (Target i).functionField :=
    functionField_isFractionRing_of_isAffineOpen (Target i) (chartOpen i b) (chart_affine i b)
  letI : IsFractionRing (S i b) Model.functionField :=
    functionField_isFractionRing_of_isAffineOpen Model (completedMap i ⁻¹ᵁ chartOpen i b)
      ((chart_affine i b).preimage (completedMap i))
  have h := FiniteFlatGenericRank318.affine_rank_eq_fraction_degree
    (R i b) (S i b) (Target i).functionField Model.functionField p
  rw [Scheme.Hom.finrank_SpecMap_algebraMap] at h
  exact h.trans (CompletedCharacterDegree318.actual_generic_degree_eight i)
lemma principal_basis (p : PrimeSpectrum (R i b)) : ∃ r : R i b, r ∉ p.asIdeal ∧ Nonempty
    (Module.Basis (Fin 8) (Localization.Away r) (LocalizedModule.Away r (S i b))) := by
  letI := finitePresentation i b
  letI := flat i b
  exact FiniteFlatPrincipalBasis318.exists_basis_of_rank (R i b) (S i b) p 8 (rank_eight i b p)
/-- Genuine rank-eight bases on the ENTIRE original inverse images form a
cover for each original character map, not merely a generic unramified subset. -/
lemma cover (i : Fin 4) (x : Target i) : ∃ (b : Bool) (r : Γ(Target i,chartOpen i b)),
    x ∈ (Target i).basicOpen r ∧ Nonempty
      (Module.Basis (Fin 8) Γ(Target i,(Target i).basicOpen r)
        Γ(Model,completedMap i ⁻¹ᵁ (Target i).basicOpen r)) := by
  obtain ⟨b,hb⟩ := chart_cover i x
  letI : Nonempty (chartOpen i b) := ⟨⟨x,hb⟩⟩
  let p : PrimeSpectrum (R i b) := (chart_affine i b).primeIdealOf ⟨x,hb⟩
  obtain ⟨r,hr,⟨bs⟩⟩ := principal_basis i b p
  refine ⟨b,r,?_,⟨AffinePrincipalBasis318.basis (completedMap i) (chartOpen i b) r
    (chart_affine i b) ((chart_affine i b).preimage (completedMap i)) bs⟩⟩
  have hp : (chart_affine i b).fromSpec p ∈ (Target i).basicOpen r := by
    change p ∈ (chart_affine i b).fromSpec ⁻¹ᵁ (Target i).basicOpen r
    rw [(chart_affine i b).fromSpec_preimage_basicOpen r]
    exact hr
  simpa only [p, IsAffineOpen.fromSpec_primeIdealOf] using hp
end CharacterActualPrincipalBasis318
