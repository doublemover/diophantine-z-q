module
public import VaryingParameterPointFamily318
public import AffineClosedQuotientExtraction318
public section
noncomputable section
namespace VaryingParameterPointIdeal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingParameterPoint318.Point R A ι S)
/-- Intrinsic full ideal of the actual pulled-back universal closed family.
This is defined for every R-point, whether or not its quotient is free. -/
@[expose] def ideal : Ideal (S ⊗[R] A) :=
  AffineClosedQuotientExtraction318.ideal (S ⊗[R] A) (VaryingParameterPointFamily318.intoSource R A ι S x)
@[expose] def comparison : VaryingParameterPointFamily318.family R A ι S x ≅
    Spec (CommRingCat.of ((S ⊗[R] A) ⧸ ideal R A ι S x)) :=
  AffineClosedQuotientExtraction318.comparison (S ⊗[R] A) (VaryingParameterPointFamily318.intoSource R A ι S x)
@[reassoc] lemma comparison_into : (comparison R A ι S x).hom ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal R A ι S x)))=
    VaryingParameterPointFamily318.intoSource R A ι S x :=
  AffineClosedQuotientExtraction318.comparison_into (S ⊗[R] A) _
lemma unique (J : Ideal (S ⊗[R] A))
    (e : VaryingParameterPointFamily318.family R A ι S x ≅ Spec (CommRingCat.of ((S ⊗[R] A) ⧸ J)))
    (h : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))=
      VaryingParameterPointFamily318.intoSource R A ι S x) : ideal R A ι S x=J :=
  AffineClosedQuotientExtraction318.ideal_unique (S ⊗[R] A) _ J e h
end VaryingParameterPointIdeal318
