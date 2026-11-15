module
public import OriginalStructureInjectivePresentation318
public section
noncomputable section
namespace InjectiveCoverCocycle318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalStructureInjectivePresentation318
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : Scheme.{0}) {ι : Type} (U : ι → X.Opens)
/-- Actual local lifts of one actual global quotient-sheaf section. -/
structure Lifts (t : (Q X).obj.obj (op ⊤)) where
  value : ∀ i, (I X).obj.obj (op (U i))
  image : ∀ i, (projection X).hom.app (op (U i)) (value i) =
    AdditiveSheafSections318.res (Q X) le_top t
variable {X U}
lemma inclusion_restrict {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)) :
    (inclusion X).hom.app (op V) (InfinitesimalUnitCocycle318.restrict X h a) =
      AdditiveSheafSections318.res (I X) h ((inclusion X).hom.app (op W) a) :=
  (AdditiveSheafSections318.hom_res (inclusion X) h a).symm
variable {t : (Q X).obj.obj (op ⊤)} (a : Lifts X U t)
/-- The positive finite-minus-infinity difference matches the ACTUAL site
Mayer-Vietoris delta, defined by extClass.precomp without an extra sign. -/
@[expose] def difference (i j : ι) : (I X).obj.obj (op (U i ⊓ U j)) :=
  AdditiveSheafSections318.res (I X) inf_le_left (a.value i) -
    AdditiveSheafSections318.res (I X) inf_le_right (a.value j)
lemma difference_image (i j : ι) :
    (projection X).hom.app (op (U i ⊓ U j)) (difference a i j) = 0 := by
  unfold difference
  rw [map_sub, ← AdditiveSheafSections318.hom_res, ← AdditiveSheafSections318.hom_res,
    a.image, a.image]
  simp only [AdditiveSheafSections318.res_res, sub_self]
lemma coefficient_exists (i j : ι) : ∃ x : Γ(X,U i ⊓ U j),
    (inclusion X).hom.app (op (U i ⊓ U j)) x = difference a i j :=
  TopCat.Sheaf.sections_exact_of_left_exact (shortExact X).exact (shortExact X).mono_f
    (difference a i j) (difference_image a i j)
@[expose] def coefficient (i j : ι) : Γ(X,U i ⊓ U j) := (coefficient_exists a i j).choose
lemma coefficient_spec (i j : ι) :
    (inclusion X).hom.app (op (U i ⊓ U j)) (coefficient a i j) = difference a i j :=
  (coefficient_exists a i j).choose_spec
@[expose] def cocycle : InfinitesimalUnitCocycle318.AdditiveCocycle X U where
  transition := coefficient a
  diagonal i := by
    apply AdditiveSheafSections318.app_injective (inclusion X) (U i ⊓ U i)
    rw [coefficient_spec, map_zero]
    exact sub_self _
  triple i j k := by
    apply AdditiveSheafSections318.app_injective (inclusion X) ((U i ⊓ U j) ⊓ U k)
    rw [map_add, inclusion_restrict, inclusion_restrict, inclusion_restrict,
      coefficient_spec, coefficient_spec, coefficient_spec]
    simp only [difference, map_sub, AdditiveSheafSections318.res_res]
    abel
/-- Actual affine lifting handles every member, including empty members, of an
arbitrary indexed affine family; no two-chart or finiteness restriction is used. -/
@[expose] def affine {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (t : (Q X).obj.obj (op ⊤)) : Lifts X U t where
  value i := (affine_lift X (U i) (hU i) (AdditiveSheafSections318.res (Q X) le_top t)).choose
  image i := (affine_lift X (U i) (hU i) (AdditiveSheafSections318.res (Q X) le_top t)).choose_spec
variable {κ : Type} (V : κ → X.Opens) (r : κ → ι) (hr : ∀ k, V k ≤ U (r k))
/-- Refinement restricts the actual chosen I-sections, rather than choosing an
unrelated lift after changing the cover. -/
@[expose] def refine : Lifts X V t where
  value k := AdditiveSheafSections318.res (I X) (hr k) (a.value (r k))
  image k := by
    rw [← AdditiveSheafSections318.hom_res, a.image, AdditiveSheafSections318.res_res]
lemma refine_coefficient (k l : κ) :
    coefficient (refine a V r hr) k l =
      InfinitesimalUnitCocycle318.restrict X (inf_le_inf (hr k) (hr l))
        (coefficient a (r k) (r l)) := by
  apply AdditiveSheafSections318.app_injective (inclusion X) (V k ⊓ V l)
  rw [coefficient_spec, inclusion_restrict, coefficient_spec]
  simp only [difference, refine, map_sub, AdditiveSheafSections318.res_res]
end InjectiveCoverCocycle318
