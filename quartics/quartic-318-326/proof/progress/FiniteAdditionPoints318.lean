module
public import FiniteAdditionGluing318
public import RelativeChordPoints318
public import TangentOpenPoints318
public import InfinityAdditionPoints318
public section
noncomputable section
namespace FiniteAdditionPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeChordAlgebra318 (PairRing)
open FiniteAdditionLocal318 FiniteAdditionGluing318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N

/-- The genuine completed Scheme point obtained from the glued finite-input morphism. -/
@[expose] def outputSchemePoint (φ:PairRing A B →ₐ[OpenJModel318.Base N] K) :
    CompletedFieldPoints318.SchemePoints (K:=K) A B :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ coordinateAddition A B hD,by
    rw [Category.assoc,coordinate_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap⟩

@[expose] def outputPoint (φ:PairRing A B →ₐ[OpenJModel318.Base N] K) :
    (LiteralWeierstrassPoints318.model (K:=K) N).Point :=
  LiteralCompletedPoints318.fieldPointEquiv N (outputSchemePoint N φ)

/-- Evaluating a localization lift recovers the actual chosen local addition map. -/
theorem output_restriction (i:Fin 4) (ψ:LocalRing A B i →ₐ[OpenJModel318.Base N] K) :
    (outputSchemePoint N (ψ.comp (inputMap A B i))).val=
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
    (f:ShortAffineJacobian318.Ring A B →ₐ[OpenJModel318.Base N] K)
    (p:CompletedFieldPoints318.SchemePoints (K:=K) A B)
    (hp:p.val=Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassGluing318.finiteChart A B) :
    LiteralCompletedPoints318.fieldPointEquiv N p=RelativeChordPoints318.pointOfHom N f := by
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
  rw [he,LiteralCompletedPoints318.fieldPointEquiv_finite]
  exact (RelativeChordPoints318.pointOfHom_scheme N f).symm

lemma chord_output (ψ:RelativeChordAlgebra318.ChordRing A B →ₐ[OpenJModel318.Base N] K) :
    outputPoint N (ψ.comp (inputMap A B 0))=
      RelativeChordPoints318.pointOfHom N (ψ.comp (RelativeChordAlgebra318.chordMap A B)) := by
  apply completed_finite_reading N (ψ.comp (RelativeChordAlgebra318.chordMap A B))
    (outputSchemePoint N (ψ.comp (inputMap A B 0)))
  rw [output_restriction N 0 ψ]
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=_
  rw [←Category.assoc]
  change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (RelativeChordAlgebra318.chordMap A B).toRingHom)) ≫ _=_
  rw [←Spec.map_comp]
  rfl

lemma tangent_output (ψ:TangentOpenAlgebra318.TangentRing A B →ₐ[OpenJModel318.Base N] K) :
    outputPoint N (ψ.comp (inputMap A B 1))=
      RelativeChordPoints318.pointOfHom N (ψ.comp (TangentOpenAlgebra318.tangentMap A B)) := by
  apply completed_finite_reading N (ψ.comp (TangentOpenAlgebra318.tangentMap A B))
    (outputSchemePoint N (ψ.comp (inputMap A B 1)))
  rw [output_restriction N 1 ψ]
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=_
  rw [←Category.assoc]
  change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TangentOpenAlgebra318.tangentMap A B).toRingHom)) ≫ _=_
  rw [←Spec.map_comp]
  rfl

lemma infinity_output (t:Bool)
    (ψ:InfinityAdditionAlgebra318.OutputRing A B t →ₐ[OpenJModel318.Base N] K) :
    outputPoint N (ψ.comp (InfinityAdditionAlgebra318.pairMap A B t))=
      InfinityAdditionPoints318.outputPoint N t ψ := by
  unfold outputPoint InfinityAdditionPoints318.outputPoint
  congr 1
  apply Subtype.ext
  cases t
  · exact output_restriction N 2 ψ
  · exact output_restriction N 3 ψ

@[expose] def lift (φ:PairRing A B →ₐ[OpenJModel318.Base N] K) (i:Fin 4)
    (hu:IsUnit (φ (FinitePairCover318.chartElement A B i))) : LocalRing A B i →ₐ[OpenJModel318.Base N] K :=
  IsLocalization.Away.liftAlgHom (f:=φ) (FinitePairCover318.chartElement A B i) hu

lemma lift_input (φ:PairRing A B →ₐ[OpenJModel318.Base N] K) (i:Fin 4)
    (hu:IsUnit (φ (FinitePairCover318.chartElement A B i))) :
    (lift N φ i hu).comp (inputMap A B i)=φ := by
  apply AlgHom.ext
  intro a
  exact IsLocalization.Away.lift_eq (S:=LocalRing A B i) (g:=φ.toRingHom)
    (FinitePairCover318.chartElement A B i) hu a

/-- Evaluation of the genuinely glued morphism equals Mathlib addition for every finite-input pair. -/
theorem actual_add [DecidableEq K] (φ:PairRing A B →ₐ[OpenJModel318.Base N] K) :
    outputPoint N φ=
      RelativeChordPoints318.pointOfHom N (φ.comp (RelativeChordAlgebra318.leftPair A B))+
      RelativeChordPoints318.pointOfHom N (φ.comp (RelativeChordAlgebra318.rightPair A B)) := by
  by_cases hg:φ (RelativeChordAlgebra318.gap A B)=0
  · by_cases hs:φ (TangentOpenAlgebra318.ordinateSum A B)=0
    · by_cases hc:φ (InfinityAdditionAlgebra318.numeratorY A B false)=0
      · have ht : φ (InfinityAdditionAlgebra318.numeratorY A B true)≠0 := fun ht =>
          FinitePairCover318.not_all_zero A B hD φ.toRingHom hg hs hc ht
        have hu : IsUnit (φ (FinitePairCover318.chartElement A B 3)) := isUnit_iff_ne_zero.mpr ht
        let ψ := lift N φ 3 hu
        have he := lift_input N φ 3 hu
        have hd : ψ (InfinityAdditionAlgebra318.pairMap A B true
            (InfinityAdditionAlgebra318.denominator A B true))=0 := by
          change (ψ.comp (inputMap A B 3)) (TangentOpenAlgebra318.ordinateSum A B)=0
          rw [he]; exact hs
        rw [←he]
        change outputPoint N (ψ.comp (InfinityAdditionAlgebra318.pairMap A B true))=_
        rw [infinity_output N true ψ]
        exact InfinityAdditionPoints318.zero_denominator_add N true ψ hd
      · have hu : IsUnit (φ (FinitePairCover318.chartElement A B 2)) := isUnit_iff_ne_zero.mpr hc
        let ψ := lift N φ 2 hu
        have he := lift_input N φ 2 hu
        have hd : ψ (InfinityAdditionAlgebra318.pairMap A B false
            (InfinityAdditionAlgebra318.denominator A B false))=0 := by
          change (ψ.comp (inputMap A B 2)) (RelativeChordAlgebra318.gap A B)=0
          rw [he]; exact hg
        rw [←he]
        change outputPoint N (ψ.comp (InfinityAdditionAlgebra318.pairMap A B false))=_
        rw [infinity_output N false ψ]
        exact InfinityAdditionPoints318.zero_denominator_add N false ψ hd
    · have hu : IsUnit (φ (FinitePairCover318.chartElement A B 1)) := isUnit_iff_ne_zero.mpr hs
      let ψ := lift N φ 1 hu
      have he := lift_input N φ 1 hu
      rw [←he,tangent_output N ψ]
      exact TangentOpenPoints318.tangent_add N ψ
  · have hu : IsUnit (φ (FinitePairCover318.chartElement A B 0)) := isUnit_iff_ne_zero.mpr hg
    let ψ := lift N φ 0 hu
    have he := lift_input N φ 0 hu
    rw [←he,chord_output N ψ]
    exact RelativeChordPoints318.chord_add N ψ

end FiniteAdditionPoints318
