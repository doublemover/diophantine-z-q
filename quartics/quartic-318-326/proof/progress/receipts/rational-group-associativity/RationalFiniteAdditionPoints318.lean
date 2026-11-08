module
public import FiniteAdditionGluing318
public import RationalChordPoints318
public import RationalTangentPoints318
public import RationalInfinityPoints318
public section
noncomputable section
namespace RationalFiniteAdditionPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeChordAlgebra318 (PairRing)
open FiniteAdditionLocal318 FiniteAdditionGluing318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {K:Type} [Field K] [Algebra ℚ K]
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2)))
include hD

/-- The genuine completed Scheme point obtained from the glued finite-input morphism. -/
@[expose] def outputSchemePoint (φ:PairRing A B →ₐ[ℚ] K) :
    CompletedFieldPoints318.SchemePoints (K:=K) A B :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ coordinateAddition A B hD,by
    rw [Category.assoc,coordinate_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap⟩

@[expose] def outputPoint (φ:PairRing A B →ₐ[ℚ] K) :
    (RationalWeierstrassPoints318.model (K:=K) A B hD).Point :=
  RationalCompletedPoints318.fieldPointEquiv A B hD (outputSchemePoint A B hD φ)

/-- Evaluating a localization lift recovers the actual chosen local addition map. -/
theorem output_restriction (i:Fin 4) (ψ:LocalRing A B i →ₐ[ℚ] K) :
    (outputSchemePoint A B hD (ψ.comp (inputMap A B i))).val=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ localAddition A B i := by
  change Spec.map (CommRingCat.ofHom (ψ.comp (inputMap A B i)).toRingHom) ≫
      coordinateAddition A B hD=_
  change Spec.map (CommRingCat.ofHom (inputMap A B i).toRingHom ≫
      CommRingCat.ofHom ψ.toRingHom) ≫ coordinateAddition A B hD=_
  rw [Spec.map_comp,Category.assoc]
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      ((FinitePairSchemeCover318.coordinateCover A B hD).f i ≫ coordinateAddition A B hD)=_
  rw [coordinate_restriction]

/-- Exact interpretation of any finite output in the completed point equivalence. -/
lemma completed_finite_reading
    (f:ShortAffineJacobian318.Ring A B →ₐ[ℚ] K)
    (p:CompletedFieldPoints318.SchemePoints (K:=K) A B)
    (hp:p.val=Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassGluing318.finiteChart A B) :
    RationalCompletedPoints318.fieldPointEquiv A B hD p=RationalChordPoints318.pointOfHom A B hD f := by
  let q := (AffineSchemeSolutions318.schemeSolutionEquiv A B).symm
    (AffineEquationFunctor318.ofHom A B f)
  have hq : q.val=Spec.map (CommRingCat.ofHom f.toRingHom) := by
    rw [AffineSchemeSolutions318.schemeSolutionEquiv_symm]
    have hh := (AffineEquationFunctor318.solutionEquiv A B).symm_apply_apply f
    change AffineEquationFunctor318.toHom A B (AffineEquationFunctor318.ofHom A B f)=f at hh
    rw [hh]
  have he : p=CompletedFieldPoints318.finiteInclusion A B q := by
    apply Subtype.ext
    exact hp.trans (congrArg (fun z=>z ≫ WeierstrassGluing318.finiteChart A B) hq).symm
  rw [he,RationalCompletedPoints318.fieldPointEquiv_finite]
  exact (RationalChordPoints318.pointOfHom_scheme A B hD f).symm

lemma chord_output (ψ:RelativeChordAlgebra318.ChordRing A B →ₐ[ℚ] K) :
    outputPoint A B hD (ψ.comp (inputMap A B 0))=
      RationalChordPoints318.pointOfHom A B hD (ψ.comp (RelativeChordAlgebra318.chordMap A B)) := by
  apply completed_finite_reading A B hD (ψ.comp (RelativeChordAlgebra318.chordMap A B))
    (outputSchemePoint A B hD (ψ.comp (inputMap A B 0)))
  rw [output_restriction A B hD 0 ψ]
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=_
  rw [←Category.assoc]
  change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (RelativeChordAlgebra318.chordMap A B).toRingHom)) ≫ _=_
  rw [←Spec.map_comp]
  rfl

lemma tangent_output (ψ:TangentOpenAlgebra318.TangentRing A B →ₐ[ℚ] K) :
    outputPoint A B hD (ψ.comp (inputMap A B 1))=
      RationalChordPoints318.pointOfHom A B hD (ψ.comp (TangentOpenAlgebra318.tangentMap A B)) := by
  apply completed_finite_reading A B hD (ψ.comp (TangentOpenAlgebra318.tangentMap A B))
    (outputSchemePoint A B hD (ψ.comp (inputMap A B 1)))
  rw [output_restriction A B hD 1 ψ]
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=_
  rw [←Category.assoc]
  change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TangentOpenAlgebra318.tangentMap A B).toRingHom)) ≫ _=_
  rw [←Spec.map_comp]
  rfl

lemma infinity_output (t:Bool)
    (ψ:InfinityAdditionAlgebra318.OutputRing A B t →ₐ[ℚ] K) :
    outputPoint A B hD (ψ.comp (InfinityAdditionAlgebra318.pairMap A B t))=
      RationalInfinityPoints318.outputPoint A B hD t ψ := by
  unfold outputPoint RationalInfinityPoints318.outputPoint
  congr 1
  apply Subtype.ext
  cases t
  · exact output_restriction A B hD 2 ψ
  · exact output_restriction A B hD 3 ψ

@[expose] def lift (_hD:IsUnit (-16*(4*A^3+27*B^2))) (φ:PairRing A B →ₐ[ℚ] K) (i:Fin 4)
    (hu:IsUnit (φ (FinitePairCover318.chartElement A B i))) : LocalRing A B i →ₐ[ℚ] K :=
  IsLocalization.Away.liftAlgHom (f:=φ) (FinitePairCover318.chartElement A B i) hu

lemma lift_input (φ:PairRing A B →ₐ[ℚ] K) (i:Fin 4)
    (hu:IsUnit (φ (FinitePairCover318.chartElement A B i))) :
    (lift A B hD φ i hu).comp (inputMap A B i)=φ := by
  apply AlgHom.ext
  intro a
  exact IsLocalization.Away.lift_eq (S:=LocalRing A B i) (g:=φ.toRingHom)
    (FinitePairCover318.chartElement A B i) hu a

/-- Evaluation of the genuinely glued morphism equals Mathlib addition for every finite-input pair. -/
theorem actual_add [DecidableEq K] (φ:PairRing A B →ₐ[ℚ] K) :
    outputPoint A B hD φ=
      RationalChordPoints318.pointOfHom A B hD (φ.comp (RelativeChordAlgebra318.leftPair A B))+
      RationalChordPoints318.pointOfHom A B hD (φ.comp (RelativeChordAlgebra318.rightPair A B)) := by
  by_cases hg:φ (RelativeChordAlgebra318.gap A B)=0
  · by_cases hs:φ (TangentOpenAlgebra318.ordinateSum A B)=0
    · by_cases hc:φ (InfinityAdditionAlgebra318.numeratorY A B false)=0
      · have ht : φ (InfinityAdditionAlgebra318.numeratorY A B true)≠0 := fun ht =>
          FinitePairCover318.not_all_zero A B hD φ.toRingHom hg hs hc ht
        have hu : IsUnit (φ (FinitePairCover318.chartElement A B 3)) := isUnit_iff_ne_zero.mpr ht
        let ψ := lift A B hD φ 3 hu
        have he := lift_input A B hD φ 3 hu
        have hd : ψ (InfinityAdditionAlgebra318.pairMap A B true
            (InfinityAdditionAlgebra318.denominator A B true))=0 := by
          change (ψ.comp (inputMap A B 3)) (TangentOpenAlgebra318.ordinateSum A B)=0
          rw [he]; exact hs
        rw [←he]
        change outputPoint A B hD (ψ.comp (InfinityAdditionAlgebra318.pairMap A B true))=_
        rw [infinity_output A B hD true ψ]
        exact RationalInfinityPoints318.zero_denominator_add A B hD true ψ hd
      · have hu : IsUnit (φ (FinitePairCover318.chartElement A B 2)) := isUnit_iff_ne_zero.mpr hc
        let ψ := lift A B hD φ 2 hu
        have he := lift_input A B hD φ 2 hu
        have hd : ψ (InfinityAdditionAlgebra318.pairMap A B false
            (InfinityAdditionAlgebra318.denominator A B false))=0 := by
          change (ψ.comp (inputMap A B 2)) (RelativeChordAlgebra318.gap A B)=0
          rw [he]; exact hg
        rw [←he]
        change outputPoint A B hD (ψ.comp (InfinityAdditionAlgebra318.pairMap A B false))=_
        rw [infinity_output A B hD false ψ]
        exact RationalInfinityPoints318.zero_denominator_add A B hD false ψ hd
    · have hu : IsUnit (φ (FinitePairCover318.chartElement A B 1)) := isUnit_iff_ne_zero.mpr hs
      let ψ := lift A B hD φ 1 hu
      have he := lift_input A B hD φ 1 hu
      rw [←he,tangent_output A B hD ψ]
      exact RationalTangentPoints318.tangent_add A B hD ψ
  · have hu : IsUnit (φ (FinitePairCover318.chartElement A B 0)) := isUnit_iff_ne_zero.mpr hg
    let ψ := lift A B hD φ 0 hu
    have he := lift_input A B hD φ 0 hu
    rw [←he,chord_output A B hD ψ]
    exact RationalChordPoints318.chord_add A B hD ψ

end RationalFiniteAdditionPoints318
