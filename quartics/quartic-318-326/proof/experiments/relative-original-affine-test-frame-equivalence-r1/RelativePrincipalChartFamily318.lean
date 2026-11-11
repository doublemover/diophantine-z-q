module
public import RelativePrincipalChartEquation318
public import RelativeAffineChartCartesian318
public import ClosedFamilyBaseRestriction318
public section
noncomputable section
namespace RelativePrincipalChartFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R S A : CommRingCat.{u}) [Algebra R S] [Algebra R A]
  {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ Spec R) (j : Spec A ⟶ X) [IsOpenImmersion j]
  (hj : j ≫ a=Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (c : A) (z : Spec (CommRingCat.of (A ⧸ Ideal.span ({c} : Set A))) ⟶ Z)
  (H : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({c} : Set A))))) z j p)
local notation "f" => RelativeOriginalAffineChart318.baseMap R S
local notation "J" => RelativeOriginalAffineChart318.into R S A a j hj
local notation "Q" => Spec.map (AffineQuotientPushout318.targetMap (RelativePrincipalChartEquation318.newIdeal R S A c))
local notation "e" => Spec.map (RelativePrincipalChartEquation318.quotientMap R S A c)
local notation "P" => ClosedFamilyBaseRestriction318.into a p f
include H in
lemma outer : IsPullback Q (e ≫ z) (J ≫ pullback.fst a f) p := by
  rw [RelativeOriginalAffineChart318.over_original]
  exact (RelativePrincipalChartEquation318.cartesian R S A c).paste_vert H
/-- The actual transported quotient is mapped into the WHOLE coefficient
fiber, not into an independently chosen divisor with the same support. -/
@[expose] def into : Spec (AffineQuotientPushout318.target (RelativePrincipalChartEquation318.newIdeal R S A c)) ⟶
    ClosedFamilyBaseRestriction318.family a p f :=
  (ClosedFamilyBaseRestriction318.cartesian a p f).flip.lift (Q ≫ J) (e ≫ z)
    (by simpa only [Category.assoc] using (outer R S A p a j hj c z H).w)
@[reassoc] lemma into_source : into R S A p a j hj c z H ≫ P=Q ≫ J :=
  (ClosedFamilyBaseRestriction318.cartesian a p f).flip.lift_fst _ _ _
@[reassoc] lemma into_original : into R S A p a j hj c z H ≫
    ClosedFamilyBaseRestriction318.toFamily a p f=e ≫ z :=
  (ClosedFamilyBaseRestriction318.cartesian a p f).flip.lift_snd _ _ _
lemma cartesian : IsPullback Q (into R S A p a j hj c z H) J P := by
  apply IsPullback.of_bot (v₂₁ := pullback.fst a f) (v₂₂ := p)
  · simpa only [into_original] using outer R S A p a j hj c z H
  · exact (into_source R S A p a j hj c z H).symm
  · exact (ClosedFamilyBaseRestriction318.cartesian a p f).flip
end RelativePrincipalChartFamily318
