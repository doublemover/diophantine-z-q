module
public import OriginalAffineLinePathSections318
public import OriginalOpenPullbackSections318
public section
noncomputable section
namespace OriginalAffinePathWholeSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {A B : CommRingCat.{u}} (f : A ⟶ B) (L : Line (Spec A))
  (M : Line (Spec B)) (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ M.object)

/-- The original affine section restriction is precisely the genuine
geometric unit followed by its displayed path comparison, on the entire
top open. The scalar-restriction comparison contributes no hidden map. -/
lemma restriction_direct (s : OriginalLineAffineModel318.sections A L) :
    OriginalAffineLinePathSections318.restriction f L M e s =
      e.hom.app ⊤ (OriginalOpenPullbackSections318.sectionPull (Spec.map f) L.object s) := by
  simp only [OriginalAffineLinePathSections318.restriction,
    AffineGlobalSectionCoherence318.global_hom_apply]
  rfl
end OriginalAffinePathWholeSections318
