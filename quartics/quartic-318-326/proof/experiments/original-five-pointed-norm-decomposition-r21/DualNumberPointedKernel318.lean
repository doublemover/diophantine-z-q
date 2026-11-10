module
public import SplitReductionPointedKernel318
public section
noncomputable section
namespace DualNumberPointedKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318
universe u
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ base R) (q : Y ⟶ base R)
/-- The original first projection is the actual splitting needed for pointed
forgetfulness; no unit-lifting hypothesis remains in this specialization. -/
@[expose] def equivalence : DualNumberScheme318.Class R p ≃
    SplitReductionPointedKernel318.Kernel (reduction R p) :=
  SplitReductionPointedKernel318.equivalence (reduction R p)
    (pullback.fst p (structureMap R)) (reduction_fst R p)
lemma forget_injective : Function.Injective (PointedLineDeformation318.forget (reduction R p)) :=
  SplitReductionPointedKernel318.forget_injective (reduction R p)
    (pullback.fst p (structureMap R)) (reduction_fst R p)
lemma class_eq_iff (a b : DualNumberScheme318.Class R p) : a = b ↔
    PointedLineDeformation318.forget (reduction R p) a =
      PointedLineDeformation318.forget (reduction R p) b :=
  ⟨congrArg _, fun h => forget_injective p h⟩
/-- On the existing kernel carrier, the actual pointed pullback is precisely
the existing unpointed line-class pullback along the old base-changed map. -/
lemma pullback_val (f : X ⟶ Y) (hf : f ≫ q = p) (c : DualNumberScheme318.Class R q) :
    (equivalence p (DualNumberScheme318.pullback R p q f hf c)).val =
      LineSheafPullback318.pullback (DualNumberScheme318.map R p q f hf) (equivalence q c).val :=
  DualNumberScheme318.forget_pullback R p q f hf c
/-- Actual isomorphism of underlying lines suffices for equality of pointed
classes on the genuine split thickening; the corrective scalar is constructed. -/
lemma class_eq_of_iso (L M : DualNumberScheme318.Deformation R p)
    (e : L.line.object ≅ M.line.object) :
    PointedLineDeformation318.classOf (reduction R p) L =
      PointedLineDeformation318.classOf (reduction R p) M :=
  forget_injective p (LineSheafClass318.classOf_eq e)
end DualNumberPointedKernel318
