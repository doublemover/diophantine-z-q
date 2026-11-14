module
public import OriginalLineAffineOpenHOne318
public import MayerVietorisSectionKernel318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace OriginalLineMayerVietorisQuotient318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite LineSheafClass318
open OriginalLineRestrictionAdditive318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} [IsIntegral X] (L : Line X)

/-- The unchanged original global derived H1 of the actual line. -/
abbrev H1 := Sheaf.H (additive L) 1

/-- The genuine derived Mayer-Vietoris boundary from the original line
sections on the entire original overlap. -/
def boundary (U V : X.Opens) (h : U ⊔ V = ⊤) : Γ(L.object,U ⊓ V) →+ H1 L :=
  MayerVietorisSectionKernel318.sectionBoundary (additive L) U V h

/-- No acyclicity hypothesis is supplied: it has been derived for this
original global line on both actual affine opens. -/
lemma boundary_surjective (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) : Function.Surjective (boundary L U V h) :=
  (OpenMayerVietoris318.boundary_surjective (additive L) U V h
    (OriginalLineAffineOpenHOne318.eq_zero L U hU)
    (OriginalLineAffineOpenHOne318.eq_zero L V hV)).comp
      (LocalSheafCohomologyAdditive318.zeroAddEquiv (additive L) (U ⊓ V)).symm.surjective

/-- Literal difference of the SAME original line presheaf restrictions. -/
def difference (U V : X.Opens) : (Γ(L.object,U) × Γ(L.object,V)) →+ Γ(L.object,U ⊓ V) :=
  ((L.object.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom.comp
    (AddMonoidHom.fst _ _)) -
  ((L.object.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom.comp
    (AddMonoidHom.snd _ _))

lemma kernel_eq_range (U V : X.Opens) (h : U ⊔ V = ⊤) :
    (boundary L U V h).ker = (difference L U V).range := by
  ext x
  change boundary L U V h x = 0 ↔ ∃ y, difference L U V y = x
  have hk := MayerVietorisSectionKernel318.sectionBoundary_kernel (additive L) U V h x
  change boundary L U V h x = 0 ↔
    ∃ (a : Γ(L.object,U)) (b : Γ(L.object,V)),
      L.object.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a -
        L.object.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b = x at hk
  exact hk.trans ⟨fun ⟨a,b,hab⟩ => ⟨(a,b),hab⟩,
    fun ⟨⟨a,b⟩,hab⟩ => ⟨a,b,hab⟩⟩

/-- The original global derived H1 of EVERY original line on an integral
scheme with a two-affine cover is the quotient of its original overlap
sections by its original restriction difference. -/
@[expose] def equivalence (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) : Γ(L.object,U ⊓ V) ⧸ (difference L U V).range ≃+ H1 L :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq_range L U V h).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (boundary L U V h)
      (boundary_surjective L U V hU hV h))

lemma equivalence_mk (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) (x : Γ(L.object,U ⊓ V)) :
    equivalence L U V hU hV h (QuotientAddGroup.mk x) = boundary L U V h x := rfl
end OriginalLineMayerVietorisQuotient318
