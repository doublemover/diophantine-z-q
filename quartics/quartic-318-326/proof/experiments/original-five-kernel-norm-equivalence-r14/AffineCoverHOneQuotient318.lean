module
public import MayerVietorisSectionKernel318
public import AffineCoverHOnePresentation318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace AffineCoverHOneQuotient318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} [IsIntegral X]

/-- Difference of the two original ring-section restrictions to the actual intersection. -/
@[expose] def difference (U V : X.Opens) : (Γ(X,U) × Γ(X,V)) →+ Γ(X,U ⊓ V) :=
  ((X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom.toAddMonoidHom.comp
    (AddMonoidHom.fst _ _)) -
  ((X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom.toAddMonoidHom.comp
    (AddMonoidHom.snd _ _))

theorem kernel_eq_range (U V : X.Opens) (h : U ⊔ V = ⊤) :
    (AffineCoverHOnePresentation318.boundary U V h).ker = (difference U V).range := by
  ext x
  change AffineCoverHOnePresentation318.boundary U V h x = 0 ↔ ∃ y, difference U V y = x
  have hk := MayerVietorisSectionKernel318.sectionBoundary_kernel
    (StructureAdditiveSheaf318.sheaf X) U V h x
  change AffineCoverHOnePresentation318.boundary U V h x = 0 ↔
    ∃ (a : Γ(X,U)) (b : Γ(X,V)),
      X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a -
        X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b = x at hk
  exact hk.trans ⟨fun ⟨a,b,hab⟩ => ⟨(a,b),hab⟩,
    fun ⟨⟨a,b⟩,hab⟩ => ⟨a,b,hab⟩⟩

/-- Genuine original global H1 as the quotient of original overlap functions by the original restriction difference. -/
@[expose] def equivalence (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) : Γ(X,U ⊓ V) ⧸ (difference U V).range ≃+
      SheafCohomologyRetraction318.structureH X 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq_range U V h).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (AffineCoverHOnePresentation318.boundary U V h)
      (AffineCoverHOnePresentation318.boundary_surjective U V hU hV h))

theorem equivalence_mk (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) (x : Γ(X,U ⊓ V)) :
    equivalence U V hU hV h (QuotientAddGroup.mk x) = AffineCoverHOnePresentation318.boundary U V h x := rfl
end AffineCoverHOneQuotient318
