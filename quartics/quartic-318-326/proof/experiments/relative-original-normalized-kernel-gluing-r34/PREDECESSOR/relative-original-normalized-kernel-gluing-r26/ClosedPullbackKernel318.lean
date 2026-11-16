module
public import ContactSchemeHilbertRecovery318
public section
noncomputable section
namespace ClosedPullbackKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {A B X Y : Scheme.{u}} (k : A ⟶ B) (q : A ⟶ X) (r : B ⟶ Y) (f : X ⟶ Y)
  [IsClosedImmersion q] [IsClosedImmersion r] (H : IsPullback k q r f)
/-- A true closed-family Cartesian square preserves the entire kernel
ideal sheaf, not only support or geometric fibers. -/
lemma ideal : q.ker=r.ker.comap f := by
  have h := Scheme.Hom.ker_comp_of_isIso H.flip.isoPullback.hom (pullback.fst f r)
  rw [H.flip.isoPullback_hom_fst] at h
  exact h.trans (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion r f)
end ClosedPullbackKernel318
