module
public import LiteralFiniteKernelFiber318
public import ThreeTorsionCompletedClosed318
public section
noncomputable section
namespace LiteralKernelOpenClosed318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N

/-- Actual finite-chart restriction of the actual completed tripling fiber. -/
@[expose] def intoGlobal : LiteralFiniteKernelFiber318.fiber N ⟶ ThreeTorsionTriplingFiber318.fiber A B hD :=
  pullback.lift
    (pullback.fst (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B) ≫
      WeierstrassGluing318.finiteChart A B)
    (pullback.snd (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B))
    (by simpa only [Category.assoc,LiteralFiniteKernel318.tripling] using
      (pullback.condition (f:=LiteralFiniteKernel318.tripling N) (g:=WeierstrassGluing318.infinity A B)))
@[reassoc] lemma intoGlobal_fst : intoGlobal N ≫ pullback.fst _ _=
    pullback.fst (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B) ≫
      WeierstrassGluing318.finiteChart A B := by simp only [intoGlobal,pullback.lift_fst]
@[reassoc] lemma intoGlobal_snd : intoGlobal N ≫ pullback.snd _ _=
    pullback.snd (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B) := by
  simp only [intoGlobal,pullback.lift_snd]

/-- The square is the actual finite-chart base change, not merely an equality
of images or ranks. -/
theorem isPullback : IsPullback (intoGlobal N)
    (pullback.fst (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B))
    (pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B))
    (WeierstrassGluing318.finiteChart A B) := by
  apply IsPullback.of_right _ (intoGlobal_fst N)
    (IsPullback.of_hasPullback (CompletedIteratedAddition318.tripling A B hD)
      (WeierstrassGluing318.infinity A B)).flip
  rw [intoGlobal_snd]
  exact (IsPullback.of_hasPullback (LiteralFiniteKernel318.tripling N)
    (WeierstrassGluing318.infinity A B)).flip

instance intoGlobal_open : IsOpenImmersion (intoGlobal N) :=
  MorphismProperty.of_isPullback (isPullback N).flip inferInstance

/-- The previously constructed canonical rank-eight map is exactly the
finite-fiber isomorphism followed by this actual open base change. -/
theorem canonical_eq : ThreeTorsionTriplingFiber318.toFiber A B hD=
    (LiteralFiniteKernelFiber318.iso N).hom ≫ intoGlobal N := by
  apply pullback.hom_ext
  · simp only [Category.assoc,ThreeTorsionTriplingFiber318.toFiber_fst,intoGlobal_fst,
      LiteralFiniteKernelFiber318.iso,LiteralFiniteKernelFiber318.toFiber_fst_assoc,
      ThreeTorsionCompletedDoubling318.inclusion]
  · simp only [Category.assoc,ThreeTorsionTriplingFiber318.toFiber_snd,intoGlobal_snd,
      LiteralFiniteKernelFiber318.iso,LiteralFiniteKernelFiber318.toFiber_snd]

/-- The actual rank-eight inclusion into the actual global literal tripling
fiber is open as well as closed. Its complementary component is not yet
identified with the zero section by this statement. -/
theorem canonical_open_closed :
    IsOpenImmersion (ThreeTorsionTriplingFiber318.toFiber A B hD) ∧
      IsClosedImmersion (ThreeTorsionTriplingFiber318.toFiber A B hD) := by
  constructor
  · rw [canonical_eq]
    infer_instance
  · exact ThreeTorsionCompletedClosed318.toFiber_closed A B hD
end LiteralKernelOpenClosed318
