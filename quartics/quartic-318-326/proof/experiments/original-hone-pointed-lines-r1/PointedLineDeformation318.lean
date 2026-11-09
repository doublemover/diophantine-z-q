module
public import LineClassPullbackLaws318
public import LineSheafUnit318
public import IdentityCotangent318
public section
noncomputable section
namespace PointedLineDeformation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X)
/-- An actual framed line sheaf on the thickening, together with a specified
trivialization of its actual restriction to the special fiber. The carrier makes
sense for any reduction map; its dual-number specialization is separate. -/
structure Deformation where
  line : Line X
  trivialization : (Scheme.Modules.pullback i).obj line.object ≅
    SheafOfModules.unit X₀.ringCatSheaf
/-- Isomorphisms retain the special-fiber framing, rather than forgetting it. -/
structure PointedIso (L M : Deformation i) where
  iso : L.line.object ≅ M.line.object
  compatible : (Scheme.Modules.pullback i).map iso.hom ≫ M.trivialization.hom =
    L.trivialization.hom
namespace PointedIso
@[expose] def refl (L : Deformation i) : PointedIso i L L where
  iso := Iso.refl _
  compatible := by simp
@[expose] def symm {L M : Deformation i} (e : PointedIso i L M) : PointedIso i M L where
  iso := e.iso.symm
  compatible := by
    change (Scheme.Modules.pullback i).map e.iso.inv ≫ L.trivialization.hom = _
    rw [← e.compatible, ← Category.assoc, ← Functor.map_comp]
    simp
@[expose] def trans {L M N : Deformation i} (e : PointedIso i L M)
    (f : PointedIso i M N) : PointedIso i L N where
  iso := e.iso ≪≫ f.iso
  compatible := by
    change (Scheme.Modules.pullback i).map (e.iso.hom ≫ f.iso.hom) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, f.compatible, e.compatible]
end PointedIso
@[expose] def pointedSetoid : Setoid (Deformation i) where
  r L M := Nonempty (PointedIso i L M)
  iseqv := ⟨fun L => ⟨PointedIso.refl i L⟩,
    fun ⟨e⟩ => ⟨PointedIso.symm i e⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨PointedIso.trans i e f⟩⟩
abbrev Class := Quotient (pointedSetoid i)
@[expose] def classOf (L : Deformation i) : Class i := Quotient.mk _ L
lemma classOf_eq_iff (L M : Deformation i) :
    classOf i L = classOf i M ↔ Nonempty (PointedIso i L M) := Quotient.eq
/-- Forgetting the specified frame maps to the EXISTING actual line-sheaf classes. -/
@[expose] def forget : Class i → LineSheafClass318.Class X :=
  Quotient.map (fun L => L.line) (fun _ _ ⟨e⟩ => ⟨e.iso⟩)
lemma forget_classOf (L : Deformation i) :
    forget i (classOf i L) = LineSheafClass318.classOf L.line := rfl
lemma special_fiber_trivial (c : Class i) :
    LineSheafPullback318.pullback i (forget i c) = LineSheafUnit318.unitClass X₀ := by
  induction c using Quotient.inductionOn with
  | h L => exact LineSheafClass318.classOf_eq L.trivialization
/-- The basepoint is the actual structure line with its canonical pullback frame. -/
@[expose] def trivial : Deformation i where
  line := LineSheafUnit318.line X
  trivialization := IdentityCotangent318.pullbackUnitIso i
end PointedLineDeformation318
