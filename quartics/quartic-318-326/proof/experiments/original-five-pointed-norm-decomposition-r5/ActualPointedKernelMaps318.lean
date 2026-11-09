module
public import OriginalFivePointedNorms318
public section
noncomputable section
namespace ActualPointedKernelMaps318
open AlgebraicGeometry CategoryTheory
open DualNumberScheme318
universe u
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ base R) (q : Y ⟶ base R)
/-- The original subgroup of actual line classes trivial on the special fiber,
with its EXISTING tensor group law. -/
abbrev Kernel := (LineClassPullbackHom318.pullback (reduction R p)).ker
@[expose] def pointedEquivalence : Class R p ≃ Kernel p where
  toFun c := ⟨PointedLineDeformation318.forget (reduction R p) c,
    PointedLineDeformation318.special_fiber_trivial (reduction R p) c⟩
  invFun c := (DualNumberPointedKernel318.equivalence p).symm ⟨c.val,c.property⟩
  left_inv c := (DualNumberPointedKernel318.equivalence p).symm_apply_apply c
  right_inv c := by
    apply Subtype.ext
    exact congrArg Subtype.val ((DualNumberPointedKernel318.equivalence p).apply_symm_apply ⟨c.val,c.property⟩)
lemma pointed_val (c : Class R p) :
    (pointedEquivalence p c).val = PointedLineDeformation318.forget (reduction R p) c := rfl
variable (f : X ⟶ Y) (hf : f ≫ q = p)
/-- Restriction of the OLD line-class pullback along the OLD thickened map.
Kernel membership follows from the actual original zero-section square. -/
@[expose] def pullback : Kernel q →* Kernel p where
  toFun c := ⟨LineClassPullbackHom318.pullback (map R p q f hf) c.val,by
    change LineClassPullbackHom318.pullback (reduction R p)
      (LineClassPullbackHom318.pullback (map R p q f hf) c.val) = 1
    rw [← MonoidHom.comp_apply,← LineClassPullbackHom318.composition,reduction_map,
      LineClassPullbackHom318.composition,MonoidHom.comp_apply,c.property,map_one]⟩
  map_one' := Subtype.ext (map_one (LineClassPullbackHom318.pullback (map R p q f hf)))
  map_mul' a b := Subtype.ext (map_mul (LineClassPullbackHom318.pullback (map R p q f hf)) a.val b.val)
lemma pointed_pullback (c : Class R q) :
    pullback p q f hf (pointedEquivalence q c) =
      pointedEquivalence p (DualNumberScheme318.pullback R p q f hf c) := by
  apply Subtype.ext
  exact (DualNumberScheme318.forget_pullback R p q f hf c).symm
end ActualPointedKernelMaps318
