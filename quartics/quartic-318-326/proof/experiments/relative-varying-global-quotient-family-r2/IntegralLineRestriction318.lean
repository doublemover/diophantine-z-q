module
public import LineSheafClass318
public import OpenLineFrameCoordinates318
public import ModuleGlobalSections318
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace IntegralLineRestriction318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] (L : Line X)

abbrev FrameIndex := {i : L.Index // Nonempty (L.opens i)}
abbrev frameOpen (i : FrameIndex L) := L.opens i.val

lemma frame_cover : ⊤ ≤ iSup (frameOpen L) := by
  intro x hx
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (L.cover hx)
  exact Opens.mem_iSup.mpr ⟨⟨i,⟨⟨x,hi⟩⟩⟩,hi⟩

/-- On an integral scheme, a section of an actual framed line that
vanishes on a nonempty open vanishes globally. The proof uses ORIGINAL
frame restrictions, injective integral structure-ring restrictions and
the genuine sheaf separatedness on a covering family. -/
lemma zero_of_restrict_zero (V : X.Opens) [Nonempty V] (s : Γ(L.object,⊤))
    (hs : L.object.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s=0) : s=0 := by
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨L.object.presheaf,L.object.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (frameOpen L) ⊤ (fun _ => homOfLE le_top) (frame_cover L) s 0
  intro i
  let W := frameOpen L i
  haveI : Nonempty W := i.property
  obtain ⟨p,hp⟩ := nonempty_preirreducible_inter W.isOpen V.isOpen
    (by obtain ⟨w⟩ := (inferInstance : Nonempty W); exact ⟨w,w.property⟩)
    (by obtain ⟨v⟩ := (inferInstance : Nonempty V); exact ⟨v,v.property⟩)
  haveI : Nonempty (W ⊓ V : X.Opens) := ⟨⟨p,hp⟩⟩
  let e := OpenLineFrameCoordinates318.frame L.object W (L.frame i.val) W le_rfl
  apply e.symm.injective
  apply map_injective_of_isIntegral X (homOfLE (show W ⊓ V ≤ W from inf_le_left))
  rw [OpenLineFrameCoordinates318.inverse_natural,
    OpenLineFrameCoordinates318.inverse_natural]
  congr 1
  rw [← Functor.map_comp_apply,← Functor.map_comp_apply,map_zero]
  have hh := congrArg
    (fun z => L.object.presheaf.map (homOfLE (show W ⊓ V ≤ V from inf_le_right)).op z) hs
  simpa only [← Functor.map_comp_apply,map_zero] using hh

/-- Therefore a nonzero global section has nonzero coefficient in EVERY
actual nonempty open line frame, not merely at a chosen generic point. -/
lemma frame_coordinate_ne_zero (s : Γ(L.object,⊤)) (hs : s≠0)
    (V : X.Opens) [Nonempty V]
    (e : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ L.object.restrict V.ι) :
    (OpenLineFrameCoordinates318.frame L.object V e V le_rfl).symm
      (L.object.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s)≠0 := by
  intro h
  apply hs
  apply zero_of_restrict_zero L V s
  apply (OpenLineFrameCoordinates318.frame L.object V e V le_rfl).symm.injective
  simpa only [map_zero] using h

/-- Actual frame coefficients of a nonzero global section are regular,
using the domain of sections on the SAME nonempty integral open. -/
theorem frame_coordinate_regular (s : Γ(L.object,⊤)) (hs : s≠0)
    (V : X.Opens) [Nonempty V]
    (e : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ L.object.restrict V.ι)
    (a : Γ(X,V))
    (ha : a * (OpenLineFrameCoordinates318.frame L.object V e V le_rfl).symm
      (L.object.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s)=0) : a=0 :=
  (mul_eq_zero.mp ha).resolve_right (frame_coordinate_ne_zero L s hs V e)
end IntegralLineRestriction318
