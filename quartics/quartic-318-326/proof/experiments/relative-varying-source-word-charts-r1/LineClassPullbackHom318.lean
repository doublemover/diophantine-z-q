module
public import TensorPullbackCocycle318
public import LineSheafClassGroup318
public import LineClassPullbackLaws318
public section
noncomputable section
namespace LineClassPullbackHom318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}}

/-- Tensor compatibility for arbitrary original line presentations, using their
actual common refinement. The line objects themselves are not replaced. -/
@[expose] def tensorIso (f : X ⟶ Y) (L N : Line Y) :
    (LineSheafPullback318.line f (LineSheafTensor318.line L N)).object ≅
      (LineSheafTensor318.line (LineSheafPullback318.line f L)
        (LineSheafPullback318.line f N)).object :=
  TensorPullbackCocycle318.comparison f (fun p : L.Index × N.Index => L.opens p.1 ⊓ N.opens p.2)
    L.object N.object
    (fun p => OpenLineFrameRefinement318.frame L.object (L.opens p.1) (L.frame p.1)
      (L.opens p.1 ⊓ N.opens p.2) inf_le_left)
    (fun p => OpenLineFrameRefinement318.frame N.object (N.opens p.2) (N.frame p.2)
      (L.opens p.1 ⊓ N.opens p.2) inf_le_right)
    (UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover)

lemma pullback_one (f : X ⟶ Y) : LineSheafPullback318.pullback f 1 = 1 :=
  classOf_eq (IdentityCotangent318.pullbackUnitIso f)

lemma pullback_mul (f : X ⟶ Y) (c d : Class Y) :
    LineSheafPullback318.pullback f (c * d) =
      LineSheafPullback318.pullback f c * LineSheafPullback318.pullback f d := by
  induction c, d using Quotient.inductionOn₂ with
  | h L N => exact classOf_eq (tensorIso f L N)

/-- The original class pullback is a group homomorphism for every scheme map.
This is a prerequisite for relative Picard quotients, not representability. -/
@[expose] def pullback (f : X ⟶ Y) : Class Y →* Class X where
  toFun := LineSheafPullback318.pullback f
  map_one' := pullback_one f
  map_mul' := pullback_mul f

lemma apply_eq (f : X ⟶ Y) (c : Class Y) :
    pullback f c = LineSheafPullback318.pullback f c := rfl

lemma on_representatives (f : X ⟶ Y) (L : Line Y) :
    pullback f (classOf L) = classOf (LineSheafPullback318.line f L) := rfl

lemma identity : pullback (𝟙 X) = MonoidHom.id (Class X) := by
  ext c
  exact LineClassPullbackLaws318.pullback_identity c

lemma composition (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  ext c
  exact LineClassPullbackLaws318.pullback_composition f g c

lemma maps_inverse (f : X ⟶ Y) (c : Class Y) :
    pullback f (c⁻¹) = (pullback f c)⁻¹ := map_inv (pullback f) c

lemma maps_power (f : X ⟶ Y) (c : Class Y) (n : ℕ) :
    pullback f (c ^ n) = (pullback f c) ^ n := map_pow (pullback f) c n
end LineClassPullbackHom318
