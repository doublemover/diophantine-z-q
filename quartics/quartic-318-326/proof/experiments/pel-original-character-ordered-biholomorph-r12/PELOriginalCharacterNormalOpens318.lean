module
public import PELOriginalWholeCharacterFlat318
public import NormalAffineOpen318
public section
noncomputable section
namespace PELOriginalCharacterNormalOpens318
open AlgebraicGeometry CategoryTheory
open PELOriginalOrderedCharacterCoordinates318 PELOriginalWholeCharacterMorphisms318

@[expose] def finiteOpen (i:Fin 4):(Curve i).Opens:=
  (WeierstrassGluing318.finiteChart (A i) (B i)).opensRange
@[expose] def infinityOpen (i:Fin 4):(Curve i).Opens:=
  (WeierstrassGluing318.infinityChart (A i) (B i)).opensRange
lemma finite_affine (i:Fin 4):IsAffineOpen (finiteOpen i):=isAffineOpen_opensRange _
lemma infinity_affine (i:Fin 4):IsAffineOpen (infinityOpen i):=isAffineOpen_opensRange _

lemma discriminant_unit (i:Fin 4):IsUnit (-16*(4*(A i)^3+27*(B i)^2)):=
  isUnit_iff_ne_zero.mpr (NormalizedLegendreProjectiveModel318.discriminant_ne
    (PELOriginalOrderedCharacterCoordinate318.parameter i)
    (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).1
    (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).2)

/-- These are normality assertions for sections over the actual entire
open images, transported along the exact chart section isomorphisms. -/
theorem finite_normal (i:Fin 4):IsIntegrallyClosed Γ(Curve i,finiteOpen i):=by
  letI:=FieldWeierstrassDedekind318.affine (A i) (B i) (discriminant_unit i)
  exact NormalAffineOpen318.sections_normal
    (CommRingCat.of (ShortAffineJacobian318.Ring (A i) (B i)))
    (WeierstrassGluing318.finiteChart (A i) (B i))
theorem infinity_normal (i:Fin 4):IsIntegrallyClosed Γ(Curve i,infinityOpen i):=by
  letI:=FieldWeierstrassDedekind318.infinity (A i) (B i) (discriminant_unit i)
  exact NormalAffineOpen318.sections_normal
    (CommRingCat.of (InfinityChart318.Ring (A i) (B i)))
    (WeierstrassGluing318.infinityChart (A i) (B i))

private lemma opensRange_nonempty {X Y:Scheme} (j:X⟶Y) [IsOpenImmersion j]
    [Nonempty X]:Nonempty j.opensRange:=by
  obtain ⟨x⟩:=‹Nonempty X›
  exact ⟨⟨j x,⟨x,rfl⟩⟩⟩
lemma finite_nonempty (i:Fin 4):Nonempty (finiteOpen i):=by
  letI:=AffineCoordinateDomain318.affine_domain (A i) (B i)
  exact opensRange_nonempty (WeierstrassGluing318.finiteChart (A i) (B i))
lemma infinity_nonempty (i:Fin 4):Nonempty (infinityOpen i):=by
  letI:=InfinityCoordinateDomain318.infinity_domain (A i) (B i)
  exact opensRange_nonempty (WeierstrassGluing318.infinityChart (A i) (B i))
lemma covers (i:Fin 4) (p:Curve i):p∈finiteOpen i ∨ p∈infinityOpen i:=
  WeierstrassGluing318.charts_cover (A i) (B i) p
end PELOriginalCharacterNormalOpens318
