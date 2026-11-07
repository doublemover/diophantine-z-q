module
public import InfinityAdditionPoints318
public import InfinityAdditionFinite318
public import TangentOpenPoints318
public section
noncomputable section
namespace InfinityAdditionLaw318
open AlgebraicGeometry CategoryTheory
open InfinityAdditionAlgebra318 InfinityAdditionScheme318 InfinityAdditionPoints318 InfinityAdditionFinite318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]

lemma pointOfHom_actualSpec (χ:ShortAffineJacobian318.Ring (OpenJAffineScheme318.A N)
    (OpenJAffineScheme318.B N) →ₐ[OpenJModel318.Base N] K) :
    (LiteralWeierstrassPoints318.fieldPointEquiv N (Spec.homEquivAlgHom.symm χ)).val=
      RelativeChordPoints318.pointOfHom N χ := by
  rw [RelativeChordPoints318.pointOfHom_scheme]
  congr 2
  change Spec.homEquivAlgHom.symm χ=Spec.homEquivAlgHom.symm
    ((AffineEquationFunctor318.solutionEquiv _ _).symm ((AffineEquationFunctor318.solutionEquiv _ _) χ))
  rw [Equiv.symm_apply_apply]

lemma point_of_finite_agreement (t:Bool)
    (φ:OutputRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t →ₐ[OpenJModel318.Base N] K)
    (χ:ShortAffineJacobian318.Ring (OpenJAffineScheme318.A N)
      (OpenJAffineScheme318.B N) →ₐ[OpenJModel318.Base N] K)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t=
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ WeierstrassGluing318.finiteChart (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) :
    outputPoint N t φ=RelativeChordPoints318.pointOfHom N χ := by
  have hp : outputSchemePoint (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) t φ=
      CompletedFieldPoints318.finiteInclusion _ _ (Spec.homEquivAlgHom.symm χ) := Subtype.ext h
  rw [outputPoint,hp,LiteralCompletedPoints318.fieldPointEquiv_finite,pointOfHom_actualSpec]

/-- The chord infinity-output Scheme morphism agrees with genuine elliptic addition on
all its actual field points, including the inverse-pair branch. -/
theorem chord_add [DecidableEq K]
    (φ:OutputRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) false →ₐ[OpenJModel318.Base N] K) :
    outputPoint N false φ=
      RelativeChordPoints318.pointOfHom N (φ.comp (leftInput (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) false))+
      RelativeChordPoints318.pointOfHom N (φ.comp (rightInput (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) false)) := by
  by_cases hd:φ (pairMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) false
      (denominator (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) false))=0
  · exact zero_denominator_add N false φ hd
  · let hu:=isUnit_iff_ne_zero.mpr hd
    let g:=chordLift (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) φ hu
    have hh:=chord_agreement (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) φ hu
    have he : outputPoint N false φ=RelativeChordPoints318.pointOfHom N
        (g.comp (RelativeChordAlgebra318.chordMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) := by
      apply point_of_finite_agreement
      rw [hh]
      dsimp only [RelativeChordScheme318.addition,RelativeChordScheme318.chordOpen,ShortAffineScheme318.scheme]
      rw [←Category.assoc,←Spec.map_comp]
      rfl
    rw [he,RelativeChordPoints318.chord_add]
    congr 1 <;> congr 1
    · apply AlgHom.ext
      intro a
      exact chordLift_left _ _ φ hu a
    · apply AlgHom.ext
      intro a
      exact chordLift_right _ _ φ hu a

/-- The complementary infinity-output Scheme morphism also agrees with actual elliptic
addition everywhere on its domain, including doubling at 2-torsion. -/
theorem tangent_add [DecidableEq K]
    (φ:OutputRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) true →ₐ[OpenJModel318.Base N] K) :
    outputPoint N true φ=
      RelativeChordPoints318.pointOfHom N (φ.comp (leftInput (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) true))+
      RelativeChordPoints318.pointOfHom N (φ.comp (rightInput (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) true)) := by
  by_cases hd:φ (pairMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) true
      (denominator (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) true))=0
  · exact zero_denominator_add N true φ hd
  · let hu:=isUnit_iff_ne_zero.mpr hd
    let g:=tangentLift (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) φ hu
    have hh:=tangent_agreement (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) φ hu
    have he : outputPoint N true φ=RelativeChordPoints318.pointOfHom N
        (g.comp (TangentOpenAlgebra318.tangentMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) := by
      apply point_of_finite_agreement
      rw [hh]
      dsimp only [TangentOpenScheme318.addition,TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
      rw [←Category.assoc,←Spec.map_comp]
      rfl
    rw [he,TangentOpenPoints318.tangent_add]
    congr 1 <;> congr 1
    · apply AlgHom.ext
      intro a
      exact tangentLift_left _ _ φ hu a
    · apply AlgHom.ext
      intro a
      exact tangentLift_right _ _ φ hu a

end InfinityAdditionLaw318
