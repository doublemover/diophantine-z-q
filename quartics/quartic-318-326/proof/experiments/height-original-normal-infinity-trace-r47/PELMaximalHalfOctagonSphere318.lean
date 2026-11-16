module
public import PELMaximalHalfOctagonShape318
public import Mathlib.Logic.Relation
public section
noncomputable section
namespace PELMaximalHalfOctagonSphere318
open Set Metric Topology
open scoped OnePoint
open PELMaximalHalfOctagonShape318 ReflectedDiskJoukowski318

@[expose] def reflectedPoint (z : centeredPolygon) : centeredPolygon :=
  ⟨reflected z.val,(polygon_reflected z.val).mpr z.property⟩

/-- The geometric pairing being proved here is the literal reflection ONLY
on the boundary of the half-octagon. It is not defined by equality in an
arithmetic or spherical quotient. -/
@[expose] def boundaryPair (z w : centeredPolygon) : Prop :=
  z.val∈frontier centeredPolygon ∧ w.val=reflected z.val

@[expose] def pairedSetoid : Setoid centeredPolygon := Relation.EqvGen.setoid boundaryPair
abbrev PairedHalfOctagon := Quotient pairedSetoid

@[expose] def sphereMap (z : centeredPolygon) : OnePoint ℂ :=
  diskMap (polygonDiskHomeomorph z)

theorem sphereMap_continuous : Continuous sphereMap :=
  ReflectedDiskJoukowskiTopology318.diskMap_continuous.comp polygonDiskHomeomorph.continuous

theorem sphereMap_surjective : Function.Surjective sphereMap :=
  diskMap_surjective.comp polygonDiskHomeomorph.surjective

theorem normalized_boundary_iff (z : centeredPolygon) :
    ‖(polygonDiskHomeomorph z).val‖=1 ↔ z.val∈frontier centeredPolygon := by
  change ‖ReflectedConvexDisk318.normalization centeredPolygon polygon_convex
    polygon_zero_neighborhood polygon_bounded z.val‖=1 ↔ z.val∈frontier centeredPolygon
  simpa only [Metric.mem_sphere,dist_zero_right] using
    ReflectedConvexDisk318.normalization_boundary_iff centeredPolygon polygon_convex
      polygon_zero_neighborhood polygon_bounded z.val

/-- Every fiber is exhausted: one interior representative, or the actual
reflected boundary partner. No density or unspecified fundamental domain
is assumed in this purely geometric six-gon statement. -/
theorem sphereMap_fibers (z w : centeredPolygon) : sphereMap z=sphereMap w ↔
    z=w ∨ boundaryPair z w := by
  change diskMap (polygonDiskHomeomorph z)=diskMap (polygonDiskHomeomorph w) ↔ _
  rw [diskMap_fibers]
  constructor
  · rintro (he | ⟨hn,hr⟩)
    · exact Or.inl (polygonDiskHomeomorph.injective he)
    · right
      refine ⟨(normalized_boundary_iff z).mp hn,?_⟩
      have he : polygonDiskHomeomorph w=polygonDiskHomeomorph (reflectedPoint z) := by
        apply Subtype.ext
        exact hr.trans (normalized_reflection z).symm
      exact congrArg Subtype.val (polygonDiskHomeomorph.injective he)
  · rintro (rfl | ⟨hb,hr⟩)
    · exact Or.inl rfl
    · right
      refine ⟨(normalized_boundary_iff z).mpr hb,?_⟩
      have hw : w=reflectedPoint z := Subtype.ext hr
      rw [hw]
      exact normalized_reflection z

theorem generated_respects (z w : centeredPolygon) (h : Relation.EqvGen boundaryPair z w) :
    sphereMap z=sphereMap w := by
  induction h with
  | rel z w h => exact (sphereMap_fibers z w).mpr (Or.inr h)
  | refl z => rfl
  | symm z w h ih => exact ih.symm
  | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem complete_generated_relation (z w : centeredPolygon) :
    Relation.EqvGen boundaryPair z w ↔ sphereMap z=sphereMap w := by
  constructor
  · exact generated_respects z w
  · intro h
    rcases (sphereMap_fibers z w).mp h with rfl | h
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h

@[expose] def comparison : PairedHalfOctagon → OnePoint ℂ :=
  Quotient.lift sphereMap generated_respects

theorem comparison_continuous : Continuous comparison :=
  sphereMap_continuous.quotient_lift generated_respects

theorem comparison_bijective : Function.Bijective comparison := by
  constructor
  · intro a b hab
    obtain ⟨z,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨w,rfl⟩ := Quotient.mk_surjective b
    exact Quotient.sound ((complete_generated_relation z w).mpr hab)
  · intro y
    obtain ⟨z,hz⟩ := sphereMap_surjective y
    exact ⟨Quotient.mk _ z,hz⟩

instance pairedCompact : CompactSpace PairedHalfOctagon := by
  apply isCompact_univ_iff.mp
  have hs : Function.Surjective (Quotient.mk pairedSetoid) := Quotient.mk_surjective
  rw [←Set.range_eq_univ.mpr hs,←Set.image_univ]
  exact isCompact_univ.image continuous_quot_mk

/-- Explicit homeomorphism from the reflected half-octagon to the independent
standard sphere. Arithmetic full-normalizer orbit comparison and a
holomorphic P1 identification remain distinct subsequent theorems. -/
@[expose] def pairedHalfOctagonSphere : PairedHalfOctagon ≃ₜ OnePoint ℂ :=
  (Equiv.ofBijective comparison comparison_bijective).toHomeomorphOfContinuousClosed
    comparison_continuous comparison_continuous.isClosedMap
end PELMaximalHalfOctagonSphere318
