module
public import InjectiveCoverCocycle318
public section
noncomputable section
namespace InjectiveCoverGauge318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalStructureInjectivePresentation318 InjectiveCoverCocycle318
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens}
    {t s : (Q X).obj.obj (op ⊤)} (a : Lifts X U t) (b : Lifts X U s)
    (d : (I X).obj.obj (op ⊤)) (hd : (projection X).hom.app (op ⊤) d = s - t)
@[expose] def correction (i : ι) : (I X).obj.obj (op (U i)) :=
  b.value i - a.value i - AdditiveSheafSections318.res (I X) le_top d
include hd in
lemma correction_image (i : ι) : (projection X).hom.app (op (U i)) (correction a b d i) = 0 := by
  unfold correction
  rw [map_sub, map_sub, b.image, a.image, ← AdditiveSheafSections318.hom_res, hd, map_sub]
  abel
include hd in
lemma gauge_exists (i : ι) : ∃ k : Γ(X,U i),
    (inclusion X).hom.app (op (U i)) k = correction a b d i :=
  TopCat.Sheaf.sections_exact_of_left_exact (shortExact X).exact (shortExact X).mono_f
    (correction a b d i) (correction_image a b d hd i)
@[expose] def gauge (i : ι) : Γ(X,U i) := (gauge_exists a b d hd i).choose
lemma gauge_spec (i : ι) :
    (inclusion X).hom.app (op (U i)) (gauge a b d hd i) = correction a b d i :=
  (gauge_exists a b d hd i).choose_spec
lemma equation (i j : ι) : (cocycle b).transition i j =
    InfinitesimalUnitCocycle318.restrict X inf_le_left (gauge a b d hd i) -
    InfinitesimalUnitCocycle318.restrict X inf_le_right (gauge a b d hd j) +
    (cocycle a).transition i j := by
  apply AdditiveSheafSections318.app_injective (inclusion X) (U i ⊓ U j)
  rw [map_add, map_sub, inclusion_restrict, inclusion_restrict, gauge_spec, gauge_spec]
  change (inclusion X).hom.app (op (U i ⊓ U j)) (coefficient b i j) =
    _ + (inclusion X).hom.app (op (U i ⊓ U j)) (coefficient a i j)
  rw [coefficient_spec, coefficient_spec]
  simp only [difference, correction, map_add, map_sub, AdditiveSheafSections318.res_res]
  abel
/-- Equality in ORIGINAL derived H1 gives an explicit additive coboundary
between arbitrary actual local lifts on the same cover. -/
lemma related (h : boundary X t = boundary X s) :
    AdditiveDeformationClasses318.Related X U (cocycle a) (cocycle b) := by
  have hz : boundary X (s - t) = 0 := by rw [map_sub, ← h, sub_self]
  obtain ⟨d,hd⟩ := (boundary_zero_iff X (s - t)).1 hz
  exact ⟨gauge a b d hd, equation a b d hd⟩
end InjectiveCoverGauge318
