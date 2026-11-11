module
public import OriginalAffineSquareZeroFrame318
public import SplitReductionPointedKernel318
public section
noncomputable section
namespace DualAffinePointedTriviality318
open AlgebraicGeometry CategoryTheory
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R]
abbrev epsilon : SquareZeroUnit318.Dual R := TrivSqZeroExt.inr 1
lemma epsilon_square : epsilon R * epsilon R = 0 := TrivSqZeroExt.inr_mul_inr _ _ _
lemma reduction_kernel : RingHom.ker (DualNumberScheme318.reductionRing R) = Ideal.span {epsilon R} := by
  apply le_antisymm
  · intro s hs
    have hf : s.fst = 0 := hs
    apply Ideal.mem_span_singleton'.2
    refine ⟨TrivSqZeroExt.inl s.snd, ?_⟩
    apply TrivSqZeroExt.ext <;> simp [epsilon, hf]
  · apply Ideal.span_le.2
    intro s hs
    rcases Set.mem_singleton_iff.mp hs with rfl
    rfl
/-- Every actual line on Spec(R[epsilon]) whose ACTUAL zero-section pullback is
trivial has an actual original module-sheaf frame, for arbitrary commutative R. -/
@[expose] def frame (L : LineSheafClass318.Line (DualNumberScheme318.test R))
    (t : (Scheme.Modules.pullback (DualNumberScheme318.zero R)).obj L.object ≅
      SheafOfModules.unit (DualNumberScheme318.base R).ringCatSheaf) :
    SheafOfModules.unit (DualNumberScheme318.test R).ringCatSheaf ≅ L.object :=
  OriginalAffineSquareZeroFrame318.frame
    (CommRingCat.ofHom (DualNumberScheme318.reductionRing R)) L t
    (TrivSqZeroExt.inlHom R R) (fun _ => rfl) (epsilon R) (epsilon_square R) (reduction_kernel R)
/-- The chosen special-fiber trivialization is respected after the existing
explicit global-unit correction along the actual split zero section. -/
@[expose] def pointedIso (L : PointedLineDeformation318.Deformation (DualNumberScheme318.zero R)) :
    PointedLineDeformation318.PointedIso (DualNumberScheme318.zero R) L
      (PointedLineDeformation318.trivial (DualNumberScheme318.zero R)) :=
  SplitReductionPointedKernel318.pointedIsoOfIso (DualNumberScheme318.zero R)
    (DualNumberScheme318.structureMap R) (DualNumberScheme318.zero_structure R) L
    (PointedLineDeformation318.trivial (DualNumberScheme318.zero R)) (frame R L.line L.trivialization).symm
lemma class_trivial (L : PointedLineDeformation318.Deformation (DualNumberScheme318.zero R)) :
    PointedLineDeformation318.classOf (DualNumberScheme318.zero R) L =
      PointedLineDeformation318.classOf (DualNumberScheme318.zero R)
        (PointedLineDeformation318.trivial (DualNumberScheme318.zero R)) :=
  (PointedLineDeformation318.classOf_eq_iff _ _ _).2 ⟨pointedIso R L⟩
/-- The whole original pointed deformation carrier on an affine split
square-zero scheme is trivial, not just the subset constructed from cocycles. -/
instance pointed_subsingleton : Subsingleton (PointedLineDeformation318.Class (DualNumberScheme318.zero R)) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M => exact (class_trivial R L).trans (class_trivial R M).symm
end DualAffinePointedTriviality318
