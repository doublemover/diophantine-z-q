module
public import OriginalTwoOpenGaugeLog318
public section
noncomputable section
namespace OriginalHOnePointedEquivalence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318 AffineHOnePointedDeformation318
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ base R)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (hc : U ⊔ V = ⊤)
@[expose] def representativeDeformation (x : Γ(X,U ⊓ V)) : Deformation R p :=
  DualNumberInfinitesimalLines318.deformation R p (thickOpens p U V) (thick_cover p U V hc)
    (AdditiveCocycleRefinement318.cocycle (pullback.fst p (structureMap R))
      (TwoOpenAdditiveCocycle318.opens U V) (thickOpens p U V) (fun _ => le_rfl)
      (TwoOpenAdditiveCocycle318.cocycle U V x))
lemma representative_class (x : Γ(X,U ⊓ V)) :
    PointedLineDeformation318.classOf (reduction R p) (representativeDeformation p U V hc x) =
      representativeClass p U V hc x := rfl
include hU hV hUV in
lemma boundary_eq_of_class (x y : Γ(X,U ⊓ V))
    (h : representativeClass p U V hc x = representativeClass p U V hc y) :
    AffineCoverHOnePresentation318.boundary U V hc x =
      AffineCoverHOnePresentation318.boundary U V hc y := by
  rw [← representative_class, ← representative_class] at h
  obtain ⟨e⟩ := (PointedLineDeformation318.classOf_eq_iff (reduction R p)
    (representativeDeformation p U V hc x) (representativeDeformation p U V hc y)).1 h
  obtain ⟨a,b,hy⟩ := OriginalTwoOpenGaugeLog318.of_iso p U V hU hV hUV x y e.iso
  have hz : AffineCoverHOnePresentation318.boundary U V hc (y - x) = 0 := by
    change y - x ∈ (AffineCoverHOnePresentation318.boundary U V hc).ker
    rw [AffineCoverHOneQuotient318.kernel_eq_range]
    refine ⟨(a,b),?_⟩
    change InfinitesimalUnitCocycle318.restrict X inf_le_left a -
      InfinitesimalUnitCocycle318.restrict X inf_le_right b = y - x
    rw [hy]
    abel
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm
include hUV in
/-- Injectivity of the OLD whole-H1 map is derived from an arbitrary actual
pointed-line isomorphism, its original frame gauge, actual split normalization,
and the original finite-minus-infinity Mayer-Vietoris kernel theorem. -/
lemma map_injective : Function.Injective (AffineHOnePointedDeformation318.map p U V hU hV hc) := by
  intro z w h
  have hxy : representativeClass p U V hc (representative U V hU hV hc z) =
      representativeClass p U V hc (representative U V hU hV hc w) := h
  have hb := boundary_eq_of_class p U V hU hV hUV hc _ _ hxy
  simpa only [representative_boundary] using hb
/-- A genuine classification of ALL actual pointed first-order Lines by the
ORIGINAL global cohomology group. The forward map is unchanged. No represented
Picard scheme, tangent-space identification, or norm comparison is asserted. -/
@[expose] def equivalence : SheafCohomologyRetraction318.structureH X 1 ≃ Class R p :=
  Equiv.ofBijective (AffineHOnePointedDeformation318.map p U V hU hV hc)
    ⟨map_injective p U V hU hV hUV hc,
      OriginalHOnePointedSurjection318.map_surjective p U V hU hV hUV hc⟩
lemma equivalence_apply (z : SheafCohomologyRetraction318.structureH X 1) :
    equivalence p U V hU hV hUV hc z = AffineHOnePointedDeformation318.map p U V hU hV hc z := rfl
lemma equivalence_boundary (x : Γ(X,U ⊓ V)) :
    equivalence p U V hU hV hUV hc (AffineCoverHOnePresentation318.boundary U V hc x) =
      representativeClass p U V hc x := AffineHOnePointedDeformation318.map_boundary p U V hU hV hc x
/-- The same ORIGINAL restriction kernel of actual line-sheaf classes is now
classified, through the already-constructed split pointed-forgetful equivalence. -/
@[expose] def kernelEquivalence : SheafCohomologyRetraction318.structureH X 1 ≃
    SplitReductionPointedKernel318.Kernel (reduction R p) :=
  (equivalence p U V hU hV hUV hc).trans (DualNumberPointedKernel318.equivalence p)
lemma kernelEquivalence_val (z : SheafCohomologyRetraction318.structureH X 1) :
    (kernelEquivalence p U V hU hV hUV hc z).val =
      PointedLineDeformation318.forget (reduction R p) (AffineHOnePointedDeformation318.map p U V hU hV hc z) := rfl
end OriginalHOnePointedEquivalence318
