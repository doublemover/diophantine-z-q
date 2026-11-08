module
public import IntrinsicOverlapSections318
public import IntrinsicFamilyFrames318
public section
noncomputable section
namespace WeierstrassIntrinsicSections318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
section Generic
variable {Y : Scheme.{u}} {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

theorem structure_of_route (f : S →ₐ[R] T) (j : Spec (CommRingCat.of S) ⟶ Y)
    (k : Spec (CommRingCat.of T) ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (route : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j=k) :
    k ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  rw [←route,Category.assoc,h,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact f.commutes

theorem open_of_route {X Z : Scheme.{u}} (f : X ⟶ Z) (j : Z ⟶ Y) (k : X ⟶ Y)
    (hf : IsOpenImmersion f) (hj : IsOpenImmersion j) (h : f ≫ j=k) : IsOpenImmersion k := by
  letI := hf
  letI := hj
  subst k
  infer_instance

theorem image_top_eq_inter {X Z W : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (k : Z ⟶ Y) [IsOpenImmersion k] (l : W ⟶ Y) [IsOpenImmersion l]
    (h : Set.range l=Set.range j ∩ Set.range k) :
    l ''ᵁ ⊤=(j ''ᵁ ⊤) ⊓ (k ''ᵁ ⊤) := by
  apply Opens.ext
  simpa only [Scheme.Hom.coe_image,Opens.coe_top,Set.image_univ,Opens.coe_inf] using h
end Generic

variable {R : Type u} [CommRing R] (A B : R)

@[expose] def xOpen : (WeierstrassGluing318.scheme A B).Opens :=
  InvariantChartCover318.finiteInto A B 0 ''ᵁ ⊤
@[expose] def finiteOpen : (WeierstrassGluing318.scheme A B).Opens :=
  InvariantChartCover318.finiteInto A B 1 ''ᵁ ⊤
@[expose] def infinityOpen : (WeierstrassGluing318.scheme A B).Opens :=
  InvariantChartCover318.infinityInto A B ''ᵁ ⊤

@[expose] def xSection : Γ(FamilyIntrinsicDifferentials318.familyOmega A B,xOpen A B) :=
  IntrinsicChartSections318.sectionMap (InvariantChartCover318.finiteInto A B 0)
    (WeierstrassGluing318.structureMap A B) (IntrinsicFamilyFrames318.finite_structure A B 0)
      (FiniteInvariantDifferential318.xForm A B)
@[expose] def finiteSection : Γ(FamilyIntrinsicDifferentials318.familyOmega A B,finiteOpen A B) :=
  IntrinsicChartSections318.sectionMap (InvariantChartCover318.finiteInto A B 1)
    (WeierstrassGluing318.structureMap A B) (IntrinsicFamilyFrames318.finite_structure A B 1)
      (InvariantChartForms318.finite A B)
@[expose] def infinitySection : Γ(FamilyIntrinsicDifferentials318.familyOmega A B,infinityOpen A B) :=
  IntrinsicChartSections318.sectionMap (InvariantChartCover318.infinityInto A B)
    (WeierstrassGluing318.structureMap A B) (IntrinsicFamilyFrames318.infinity_structure A B)
      (InvariantChartForms318.infinity A B)
end WeierstrassIntrinsicSections318
