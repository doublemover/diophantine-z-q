module
public import LocalSectionAffineChart318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public section
noncomputable section
namespace ActualCommonAffinePoint318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {A B : CommRingCat.{u}} (i : Spec A ⟶ X) (j : Spec B ⟶ X)
  (a : A ⟶ CommRingCat.of K) (b : B ⟶ CommRingCat.of K)

/-- An actual common affine chart carrying the SAME field-valued point.
The arrows to both original charts are open immersions, not merely maps
with matching function fields. -/
structure Data where
  ring : CommRingCat.{u}
  left : A ⟶ ring
  right : B ⟶ ring
  evaluation : ring ⟶ CommRingCat.of K
  left_open : IsOpenImmersion (Spec.map left)
  right_open : IsOpenImmersion (Spec.map right)
  square : Spec.map left ≫ i = Spec.map right ≫ j
  left_point : left ≫ evaluation = a
  right_point : right ≫ evaluation = b

/-- Take an affine neighborhood inside the actual categorical
intersection. The field point lies in it and factors through both of the
original chart points with exactly the original evaluation maps. -/
theorem exists_data [IsOpenImmersion i] [IsOpenImmersion j]
    (h : Spec.map a ≫ i = Spec.map b ≫ j) : Nonempty (Data i j a b) := by
  let P := pullback i j
  let q : Spec (CommRingCat.of K) ⟶ P := pullback.lift (Spec.map a) (Spec.map b) h
  let x := q (IsLocalRing.closedPoint K)
  let U : P.Opens := (P.affineCover.f (P.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := P.affineCover.covers x
  have hwhole : Set.range q ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨z,rfl⟩
    have hz : q z ∈ U :=
      ((IsLocalRing.specializes_closedPoint z).map q.continuous).mem_open U.isOpen hx
    change q z ∈ hU.fromSpec.opensRange
    rwa [hU.opensRange_fromSpec]
  let l := IsOpenImmersion.lift hU.fromSpec q hwhole
  have hl : l ≫ hU.fromSpec = q := IsOpenImmersion.lift_fac _ _ hwhole
  obtain ⟨e,he⟩ := Spec.homEquiv.symm.surjective l
  obtain ⟨f,hf⟩ := Spec.homEquiv.symm.surjective (hU.fromSpec ≫ pullback.fst i j)
  obtain ⟨g,hg⟩ := Spec.homEquiv.symm.surjective (hU.fromSpec ≫ pullback.snd i j)
  have hfopen : IsOpenImmersion (Spec.map f) := by rw [hf]; infer_instance
  have hgopen : IsOpenImmersion (Spec.map g) := by rw [hg]; infer_instance
  have hsquare : Spec.map f ≫ i = Spec.map g ≫ j := by
    rw [hf,hg,Category.assoc,Category.assoc,pullback.condition]
  have hfa : f ≫ e = a := by
    apply Spec.map_injective
    rw [Spec.map_comp,he,hf,←Category.assoc,hl]
    exact pullback.lift_fst _ _ _
  have hgb : g ≫ e = b := by
    apply Spec.map_injective
    rw [Spec.map_comp,he,hg,←Category.assoc,hl]
    exact pullback.lift_snd _ _ _
  exact ⟨⟨Γ(P,U),f,g,e,hfopen,hgopen,hsquare,hfa,hgb⟩⟩

namespace Data
variable (C : Data i j a b)
/-- Both maps are etale on the WHOLE actual common affine neighborhood. -/
theorem left_etale : C.left.hom.Etale := by
  letI := C.left_open
  exact HasRingHomProperty.Spec_iff.mp (inferInstance : Etale (Spec.map C.left))
theorem right_etale : C.right.hom.Etale := by
  letI := C.right_open
  exact HasRingHomProperty.Spec_iff.mp (inferInstance : Etale (Spec.map C.right))
/-- The common chart retains the same base-ring map through both old
charts whenever their original structure squares agree. -/
theorem scalar_square {R : CommRingCat.{u}} (p : X ⟶ Spec R)
    (s : R ⟶ A) (t : R ⟶ B) (hs : Spec.map s = i ≫ p)
    (ht : Spec.map t = j ≫ p) : s ≫ C.left = t ≫ C.right := by
  apply Spec.map_injective
  rw [Spec.map_comp,Spec.map_comp,hs,ht,←Category.assoc,←Category.assoc,C.square]
end Data
end ActualCommonAffinePoint318
