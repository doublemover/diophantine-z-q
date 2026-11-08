module
public import FiniteDoublingUnit318
public import ThreeTorsionEqualizerScheme318
public import AffineProductEvaluation318
public section
noncomputable section
namespace FiniteDoublingOpenLift318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Open-immersion factorization can be checked on actual affine Scheme
tests; the resulting lift is a genuine unique Scheme morphism. -/
theorem open_lift_of_affine_tests {U X Y:Scheme.{u}} (j:U ⟶ Y) [IsOpenImmersion j]
    (f:X ⟶ Y) (h:∀ (S:CommRingCat.{u}) (t:Spec S ⟶ X), ∃g:Spec S ⟶ U,g ≫ j=t ≫ f) :
    ∃!g:X ⟶ U,g ≫ j=f := by
  have hr:Set.range f ⊆ Set.range j := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy⟩:=X.affineOpenCover.covers x
    obtain ⟨g,hg⟩:=h (X.affineOpenCover.X (X.affineOpenCover.idx x))
      (X.affineOpenCover.f (X.affineOpenCover.idx x))
    refine ⟨g y,?_⟩
    rw [←Scheme.Hom.comp_apply,hg,Scheme.Hom.comp_apply,hy]
  exact ⟨IsOpenImmersion.lift j f hr,IsOpenImmersion.lift_fac j f hr,
    fun g hg=>IsOpenImmersion.lift_uniq j f hr g hg⟩

variable {R:Type} [CommRing R] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))

lemma affine_lift {S:Type} [CommRing S]
    (f g:Spec (CommRingCat.of S) ⟶ ShortAffineScheme318.scheme A B)
    (h:f ≫ WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.doubling A B hD=
      g ≫ WeierstrassGluing318.finiteChart A B) :
    ∃k:Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (NonverticalDoubling318.OpenRing A B)),
      k ≫ ThreeTorsionEqualizerScheme318.openInclusion A B=f := by
  obtain ⟨b,hb⟩:=Spec.map_surjective (f ≫ ShortAffineScheme318.structureMap A B)
  letI : Algebra R S:=b.hom.toAlgebra
  have hf:f ≫ Spec.algebraMap R (ShortAffineJacobian318.Ring A B)=Spec.algebraMap R S:=hb.symm
  have hg:g ≫ Spec.algebraMap R (ShortAffineJacobian318.Ring A B)=Spec.algebraMap R S := by
    have hh:=congrArg (fun k=>k ≫ WeierstrassGluing318.structureMap A B) h
    simp only [Category.assoc,CompletedIteratedAddition318.doubling_over_base,
      WeierstrassGluing318.finiteChart_structure] at hh
    exact hh.symm.trans hf
  let φ:=AffineProductEvaluation318.toAlgHom f hf
  let ψ:=AffineProductEvaluation318.toAlgHom g hg
  have hφ:Spec.map (CommRingCat.ofHom φ.toRingHom)=f:=AffineProductEvaluation318.map_toAlgHom f hf
  have hψ:Spec.map (CommRingCat.ofHom ψ.toRingHom)=g:=AffineProductEvaluation318.map_toAlgHom g hg
  have hu:IsUnit (2*φ (ShortAffineJacobian318.y A B)) := by
    apply FiniteDoublingUnit318.two_y_unit A B hD φ ψ
    simpa only [FiniteDoublingUnit318.finiteInput,hφ,hψ,Category.assoc] using h
  let k:NonverticalDoubling318.OpenRing A B →ₐ[R] S:=
    IsLocalization.Away.liftAlgHom (f:=φ) (NonverticalDoubling318.denominator A B)
      (by simpa only [NonverticalDoubling318.denominator,map_mul,map_ofNat] using hu)
  refine ⟨Spec.map (CommRingCat.ofHom k.toRingHom),?_⟩
  rw [←hφ]
  dsimp only [ThreeTorsionEqualizerScheme318.openInclusion]
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change k (NonverticalDoubling318.curveMap A B r)=φ r
  simp only [k,NonverticalDoubling318.curveMap,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl

/-- Every actual finite point with finite doubled output uniquely factors
through the genuine D(2y) open, over arbitrary coefficient bases and arbitrary
Scheme tests. Nonreduced directions are retained by the actual open lift. -/
theorem universal {X:Scheme} (f g:X ⟶ ShortAffineScheme318.scheme A B)
    (h:f ≫ WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.doubling A B hD=
      g ≫ WeierstrassGluing318.finiteChart A B) :
    ∃!k:X ⟶ Spec (CommRingCat.of (NonverticalDoubling318.OpenRing A B)),
      k ≫ ThreeTorsionEqualizerScheme318.openInclusion A B=f := by
  apply open_lift_of_affine_tests
  intro S t
  exact affine_lift A B hD (t ≫ f) (t ≫ g)
    (by simpa only [Category.assoc] using congrArg (fun k=>t ≫ k) h)
end FiniteDoublingOpenLift318
