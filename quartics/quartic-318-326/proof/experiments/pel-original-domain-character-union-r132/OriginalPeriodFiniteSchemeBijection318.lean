module
public import OriginalPeriodGlobalSchemePoints318
public import CompletedFieldPoints318
public section
noncomputable section
namespace OriginalPeriodFiniteSchemeBijection318
open CategoryTheory AlgebraicGeometry
open OriginalComplexPeriodPair318 OriginalPeriodWeierstrassCoordinates318
open OriginalPeriodProjectiveModel318 OriginalPeriodSchemeChartPoints318
open ComplexAffineFreeTranslation318
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Exact original analytic pair to native affine equation coordinates.
The factor two is forced by the independent scheme equation. -/
@[expose] def nativeSolutions :
    {p : ℂ × ℂ // p.2^2=4*p.1^3-(pair L).g₂*p.1-(pair L).g₃} ≃
      AffineEquationFunctor318.Solutions (S:=ℂ) (A L) (B L) where
  toFun p := ⟨(p.val.1,p.val.2/2),by
    have h := p.property
    change (p.val.2/2)^2-p.val.1^3-A L*p.val.1-B L=0
    dsimp [A,B]
    linear_combination h/4⟩
  invFun p := ⟨(p.val.1,2*p.val.2),by
    have h := p.property
    change p.val.2^2-p.val.1^3-A L*p.val.1-B L=0 at h
    dsimp [A,B] at h
    linear_combination 4*h⟩
  left_inv p := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> ring
  right_inv p := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> ring

/-- ALL genuine finite-chart scheme-valued complex points are obtained
from the original punctured torus, through the actual affine functor. -/
@[expose] def finiteEquivalence : {q : Torus L // q≠0} ≃
    AffineSchemeSolutions318.SchemePoints (K:=ℂ) (A L) (B L) :=
  (OriginalPeriodAffineBijection318.equivalence L).trans
    ((nativeSolutions L).trans (AffineSchemeSolutions318.schemeSolutionEquiv (A L) (B L)).symm)

lemma original_evaluation (q : {q : Torus L // q≠0}) :
    AffineEquationFunctor318.toHom (A L) (B L)
      (nativeSolutions L (affinePoint L q))=finiteEvaluation L q := by
  apply AffineEquationFunctor318.hom_ext
  · rw [AffineEquationFunctor318.toHom_x,finite_x]
    rfl
  · rw [AffineEquationFunctor318.toHom_y,finite_y]
    rfl

/-- The equivalence uses the PREVIOUS original full coordinate-ring map,
not merely a set bijection to some abstract solution carrier. -/
lemma finiteEquivalence_value (q : {q : Torus L // q≠0}) :
    (finiteEquivalence L q).val=
      Spec.map (CommRingCat.ofHom (finiteEvaluation L q).toRingHom) := by
  change ((AffineSchemeSolutions318.schemeSolutionEquiv (A L) (B L)).symm
    (nativeSolutions L (affinePoint L q))).val=_
  rw [AffineSchemeSolutions318.schemeSolutionEquiv_symm,original_evaluation]

lemma finite_inclusion (q : {q : Torus L // q≠0}) :
    (CompletedFieldPoints318.finiteInclusion (A L) (B L) (finiteEquivalence L q)).val=
      finitePoint L q := by
  change (finiteEquivalence L q).val ≫ WeierstrassGluing318.finiteChart (A L) (B L)=_
  rw [finiteEquivalence_value]
  rfl
end OriginalPeriodFiniteSchemeBijection318
