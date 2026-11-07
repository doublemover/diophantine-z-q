module
public import InfinityAdditionScheme318
public import InfinityAdditionValues318
public import LiteralCompletedPoints318
public import RelativeChordPoints318
import all WeierstrassGluing318
public section
noncomputable section
namespace InfinityAdditionPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinityAdditionAlgebra318 InfinityAdditionScheme318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R K:Type u} [CommRing R] [Field K] [Algebra R K]

/-- The actual completed Scheme point obtained by evaluating the infinity-output morphism. -/
@[expose] def outputSchemePoint (A B:R) (t:Bool) (φ:OutputRing A B t →ₐ[R] K) :
    CompletedFieldPoints318.SchemePoints (K:=K) A B :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ addition A B t,by
    rw [Category.assoc,addition_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact φ.commutes r⟩

/-- The denominator-zero branch really lands at the actual closed infinity section. -/
theorem outputSchemePoint_infinity (A B:R) (t:Bool) (φ:OutputRing A B t →ₐ[R] K)
    (hd:φ (pairMap A B t (denominator A B t))=0) :
    outputSchemePoint A B t φ=CompletedFieldPoints318.infinityPoint A B := by
  have hz : (φ.comp (outputMap A B t)) (InfinityChart318.z A B)=0 := by
    simp only [AlgHom.comp_apply,outputMap_z,outZ,map_mul,map_pow,hd]
    ring
  have hh:=CompletedFieldPoints318.infinity_hom_zero A B (φ.comp (outputMap A B t)) hz
  apply Subtype.ext
  dsimp only [outputSchemePoint,addition,chartAddition]
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((φ.comp (outputMap A B t)).toRingHom)) ≫ _=_
  rw [hh]
  change Spec.map (CommRingCat.ofHom ((algebraMap R K).comp (InfinityChart318.origin A B).toRingHom)) ≫ _=_
  rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  rfl

variable (N:ℕ) {L:Type} [Field L] [Algebra (OpenJModel318.Base N) L]

/-- The completed Scheme point is bound to the genuine literal elliptic point type. -/
@[expose] def outputPoint (t:Bool)
    (φ:OutputRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t →ₐ[OpenJModel318.Base N] L) :
    (LiteralWeierstrassPoints318.model (K:=L) N).Point :=
  LiteralCompletedPoints318.fieldPointEquiv N
    (outputSchemePoint (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t φ)

/-- Every zero-denominator field point of either actual infinity-output chart agrees
with Mathlib's actual inverse-pair addition, including doubling at 2-torsion. -/
theorem zero_denominator_add [DecidableEq L] (t:Bool)
    (φ:OutputRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t →ₐ[OpenJModel318.Base N] L)
    (hd:φ (pairMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t
      (denominator (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t))=0) :
    outputPoint N t φ=
      RelativeChordPoints318.pointOfHom N (φ.comp (leftInput (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t))+
      RelativeChordPoints318.pointOfHom N (φ.comp (rightInput (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t)) := by
  rw [outputPoint,outputSchemePoint_infinity _ _ _ _ hd,LiteralCompletedPoints318.fieldPointEquiv_infinity]
  obtain ⟨hx,hy⟩:=InfinityAdditionValues318.inverse_coordinates _ _ t φ hd
  have ha1 : (LiteralWeierstrassPoints318.model (K:=L) N).a₁=0 := by
    simp only [LiteralWeierstrassPoints318.model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  have ha3 : (LiteralWeierstrassPoints318.model (K:=L) N).a₃=0 := by
    simp only [LiteralWeierstrassPoints318.model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  unfold RelativeChordPoints318.pointOfHom LiteralWeierstrassPoints318.solutionPoint
  simp only [AffineEquationFunctor318.ofHom,AlgHom.comp_apply,leftInput,rightInput]
  change WeierstrassCurve.Affine.Point.zero=
    WeierstrassCurve.Affine.Point.some (φ (pairMap _ _ t (X1 _ _))) (φ (pairMap _ _ t (Y1 _ _))) _+
    WeierstrassCurve.Affine.Point.some (φ (pairMap _ _ t (X2 _ _))) (φ (pairMap _ _ t (Y2 _ _))) _
  symm
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq hx
  simpa only [WeierstrassCurve.Affine.negY,ha1,ha3,zero_mul,sub_zero] using hy

end InfinityAdditionPoints318
