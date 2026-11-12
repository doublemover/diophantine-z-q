module
public import OriginalNormalModelFlatFamily318
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Stalk
public section
noncomputable section
namespace LocalSectionAffineChart318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (g : Spec (CommRingCat.of R) ⟶ X)

/-- An actual affine neighborhood of the whole section, with its actual
finite-type base map and integral point map. The base is not punctured. -/
structure Data where
  ring : CommRingCat.{u}
  inclusion : Spec ring ⟶ X
  openImmersion : IsOpenImmersion inclusion
  scalar : CommRingCat.of R ⟶ ring
  evaluation : ring ⟶ CommRingCat.of R
  over_base : Spec.map scalar=inclusion ≫ f
  section_eq : Spec.map evaluation ≫ inclusion=g
  retraction : scalar ≫ evaluation=𝟙 _
  finite_type : scalar.hom.FiniteType

/-- Every point of a local spectrum specializes to its closed point, so
one actual affine neighborhood contains the ENTIRE valuative section.
The resulting maps retain the scheme section, not just its closed image. -/
theorem exists_data [LocallyOfFiniteType f] (hg : g ≫ f=𝟙 _) :
    Nonempty (Data f g) := by
  let x := g (IsLocalRing.closedPoint R)
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x∈U := X.affineCover.covers x
  have hwhole : Set.range g⊆Set.range hU.fromSpec := by
    rintro _ ⟨z,rfl⟩
    have hz : g z∈U :=
      ((IsLocalRing.specializes_closedPoint z).map g.continuous).mem_open U.isOpen hx
    change g z∈hU.fromSpec.opensRange
    rwa [hU.opensRange_fromSpec]
  let l := IsOpenImmersion.lift hU.fromSpec g hwhole
  have hl : l ≫ hU.fromSpec=g := IsOpenImmersion.lift_fac _ _ hwhole
  obtain ⟨e,he⟩ := Spec.homEquiv.symm.surjective l
  obtain ⟨s,hs⟩ := Spec.homEquiv.symm.surjective (hU.fromSpec ≫ f)
  have hret : s ≫ e=𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,he,hs,←Category.assoc,hl,hg]
    simp
  have hft : LocallyOfFiniteType (Spec.map s) := by
    rw [hs]
    infer_instance
  exact ⟨{
    ring := Γ(X,U)
    inclusion := hU.fromSpec
    openImmersion := inferInstance
    scalar := s
    evaluation := e
    over_base := hs
    section_eq := by rw [he]; exact hl
    retraction := hret
    finite_type := HasRingHomProperty.Spec_iff.mp hft }⟩

namespace Data
variable (C : Data f g)
/-- The actual affine base map is injective, since the ORIGINAL section
provides a literal retraction, not merely a nonempty special fiber. -/
theorem scalar_injective : Function.Injective C.scalar.hom := by
  intro a b h
  have hh := congrArg C.evaluation.hom h
  have ha := congrArg (fun k => k.hom a) C.retraction
  have hb := congrArg (fun k => k.hom b) C.retraction
  exact ha.symm.trans (hh.trans hb)

/-- Exact generic specialization of the SAME affine integral point. -/
theorem generic_section {K : Type u} [CommRing K] (ι : R →+* K) :
    Spec.map (CommRingCat.ofHom (ι.comp C.evaluation.hom)) ≫ C.inclusion=
      Spec.map (CommRingCat.ofHom ι) ≫ g := by
  rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,C.section_eq]
end Data
end LocalSectionAffineChart318
