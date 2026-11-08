module
public import ThreeTorsionRingCoequalizer318
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public section
noncomputable section
namespace ThreeTorsionEqualizerScheme318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ThreeTorsionAlgebra318 NonverticalDoubling318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

@[expose] def openInclusion : Spec (CommRingCat.of (OpenRing A B))⟶ShortAffineScheme318.scheme A B:=
  Spec.map (CommRingCat.ofHom (curveMap A B).toRingHom)

instance openInclusion_open : IsOpenImmersion (openInclusion A B):=by
  exact IsOpenImmersion.of_isLocalization (S:=OpenRing A B) (denominator A B)

@[expose] def doubling : Spec (CommRingCat.of (OpenRing A B))⟶ShortAffineScheme318.scheme A B:=
  Spec.map (CommRingCat.ofHom (double A B).toRingHom)
@[expose] def negation : Spec (CommRingCat.of (OpenRing A B))⟶ShortAffineScheme318.scheme A B:=
  Spec.map (CommRingCat.ofHom (negative A B).toRingHom)
@[expose] def inclusion : ThreeTorsionScheme318.scheme A B hD⟶Spec (CommRingCat.of (OpenRing A B)):=
  Spec.map (CommRingCat.ofHom (toTorsion A B hD).toRingHom)

lemma inclusion_intoCurve : inclusion A B hD≫openInclusion A B=
    ThreeTorsionScheme318.inclusion A B hD:=by
  dsimp only [inclusion,openInclusion,ThreeTorsionScheme318.inclusion]
  rw [←Spec.map_comp]
  exact congrArg (fun f:Curve A B→ₐ[R]Ring A B hD=>Spec.map (CommRingCat.ofHom f.toRingHom))
    (toTorsion_curveMap A B hD)

instance inclusion_closed : IsClosedImmersion (inclusion A B hD):=
  IsClosedImmersion.spec_of_surjective _ (ThreeTorsionRingCoequalizer318.quotient_surjective A B hD)

lemma condition : inclusion A B hD≫doubling A B=inclusion A B hD≫negation A B:=by
  dsimp only [inclusion,doubling,negation,ThreeTorsionScheme318.scheme,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:Curve A B→ₐ[R]Ring A B hD=>Spec.map (CommRingCat.ofHom f.toRingHom))
    (NonverticalDoubling318.condition A B hD)

@[expose] def fork : Fork (doubling A B) (negation A B):=
  Fork.ofι (inclusion A B hD) (condition A B hD)

/-- The actual relative rank-eight torsion scheme is the categorical
equalizer of doubling and negation on the actual nonvertical affine open.
This gives the universal property for arbitrary Scheme test objects. -/
@[expose] def isLimit : IsLimit (fork A B hD):=by
  let π:=ThreeTorsionRingCoequalizer318.quotient A B hD
  have w:=ThreeTorsionRingCoequalizer318.condition A B hD
  have wop:π.op≫(ThreeTorsionRingCoequalizer318.doubling A B).op=
      π.op≫(ThreeTorsionRingCoequalizer318.negation A B).op:=by
    exact congrArg Quiver.Hom.op w
  have hop:IsLimit (Fork.ofι π.op wop):=
    (Cofork.isColimitOfπEquivIsLimitOp π π w wop rfl)
      (ThreeTorsionRingCoequalizer318.isColimit A B hD)
  exact isLimitForkMapOfIsLimit Scheme.Spec wop hop

/-- The universal property holds for every Scheme test object, including
nonreduced and nonaffine schemes. -/
theorem universal {X:Scheme} (f:X⟶Spec (CommRingCat.of (OpenRing A B)))
    (hf:f≫doubling A B=f≫negation A B) :
    ∃!g:X⟶ThreeTorsionScheme318.scheme A B hD,g≫inclusion A B hD=f:=
  Fork.IsLimit.existsUnique (isLimit A B hD) f hf

end ThreeTorsionEqualizerScheme318
