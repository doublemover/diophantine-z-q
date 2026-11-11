module
public import RegularAffineChartFlat318
public import FlatPrincipalCoefficientRegular318
public import AffineQuotientPushout318
public section
noncomputable section
namespace RelativePrincipalChartEquation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R S A : CommRingCat.{u}) [Algebra R S] [Algebra R A] (c : A)
abbrev ring := CommRingCat.of (S ⊗[R] A)
abbrev equation : ring R S A := (1 : S) ⊗ₜ[R] c
abbrev oldIdeal := Ideal.span ({c} : Set A)
abbrev newIdeal := Ideal.span ({equation R S A c} : Set (ring R S A))
@[expose] def source : A ⟶ ring R S A :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom
lemma ideal : (oldIdeal A c).map (source R S A).hom=newIdeal R S A c :=
  FlatPrincipalCoefficientRegular318.ideal R A S c
@[expose] def quotientMap : AffineQuotientPushout318.source (oldIdeal A c) ⟶
    AffineQuotientPushout318.target (newIdeal R S A c) :=
  AffineQuotientPushout318.arrow (source R S A) (oldIdeal A c) (newIdeal R S A c) (ideal R S A c)
/-- Full quotient by the transported equation, including nilpotents,
is the genuine base change of the original whole principal quotient. -/
lemma cartesian : IsPullback
    (Spec.map (AffineQuotientPushout318.targetMap (newIdeal R S A c)))
    (Spec.map (quotientMap R S A c)) (Spec.map (source R S A))
    (Spec.map (AffineQuotientPushout318.sourceMap (oldIdeal A c))) :=
  AffineQuotientPushout318.pullback (source R S A) _ _ (ideal R S A c)
variable [hflat : Module.Flat R (A ⧸ oldIdeal A c)] (hc : ∀ x : A,x*c=0 → x=0)
include hflat hc in
lemma regular : ∀ x : ring R S A,x*equation R S A c=0 → x=0 :=
  FlatPrincipalCoefficientRegular318.regular R A S c hc
end RelativePrincipalChartEquation318
