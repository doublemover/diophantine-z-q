module
public import LiteralFiniteKernel318
public import ThreeTorsionClosed318
public section
noncomputable section
namespace LiteralFiniteKernelFiber318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N

lemma tripling_base : LiteralFiniteKernel318.tripling N ≫ WeierstrassGluing318.structureMap A B=
    ShortAffineScheme318.structureMap A B := by
  rw [LiteralFiniteKernel318.tripling,Category.assoc,CompletedIteratedAddition318.tripling_over_base,
    WeierstrassGluing318.finiteChart_structure]
lemma zero_eq : LiteralFiniteKernel318.zero N=
    ShortAffineScheme318.structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  rw [LiteralFiniteKernel318.zero,←Category.assoc,WeierstrassGluing318.finiteChart_structure]
lemma condition : ThreeTorsionScheme318.inclusion A B hD ≫ LiteralFiniteKernel318.tripling N=
    ThreeTorsionScheme318.structureMap A B hD ≫ WeierstrassGluing318.infinity A B := by
  rw [LiteralFiniteKernel318.condition,zero_eq,←Category.assoc,ThreeTorsionScheme318.inclusion_over_base]

/-- Actual pullback of the zero section by completed tripling restricted to
the entire finite chart, not a point-set kernel. -/
@[expose] def fiber : Scheme :=
  pullback (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B)
@[expose] def toFiber : ThreeTorsionScheme318.scheme A B hD ⟶ fiber N :=
  pullback.lift (ThreeTorsionScheme318.inclusion A B hD) (ThreeTorsionScheme318.structureMap A B hD)
    (condition N)
@[reassoc] lemma toFiber_fst : toFiber N ≫ pullback.fst _ _=ThreeTorsionScheme318.inclusion A B hD := by
  simp only [toFiber,pullback.lift_fst]
@[reassoc] lemma toFiber_snd : toFiber N ≫ pullback.snd _ _=ThreeTorsionScheme318.structureMap A B hD := by
  simp only [toFiber,pullback.lift_snd]
@[reassoc] lemma fiber_base :
    pullback.fst (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B) ≫
      ShortAffineScheme318.structureMap A B=pullback.snd _ _ := by
  have h:=congrArg (fun k=>k ≫ WeierstrassGluing318.structureMap A B)
    (pullback.condition (f:=LiteralFiniteKernel318.tripling N) (g:=WeierstrassGluing318.infinity A B))
  simpa only [Category.assoc,tripling_base,WeierstrassGluing318.infinity_section,Category.comp_id] using h
lemma fiber_condition :
    pullback.fst (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B) ≫
      LiteralFiniteKernel318.tripling N=pullback.fst _ _ ≫ LiteralFiniteKernel318.zero N := by
  rw [pullback.condition,zero_eq,←Category.assoc,fiber_base]

@[expose] def fromFiber : fiber N ⟶ ThreeTorsionScheme318.scheme A B hD :=
  (LiteralFiniteKernel318.universal N (pullback.fst _ _) (fiber_condition N)).choose
@[reassoc] lemma fromFiber_inclusion : fromFiber N ≫ ThreeTorsionScheme318.inclusion A B hD=
    pullback.fst (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B) :=
  (LiteralFiniteKernel318.universal N (pullback.fst _ _) (fiber_condition N)).choose_spec.1
@[reassoc] lemma fromFiber_base : fromFiber N ≫ ThreeTorsionScheme318.structureMap A B hD=
    pullback.snd (LiteralFiniteKernel318.tripling N) (WeierstrassGluing318.infinity A B) := by
  rw [←ThreeTorsionScheme318.inclusion_over_base,←Category.assoc,fromFiber_inclusion,fiber_base]

/-- The original full rank-eight torsion scheme is isomorphic to the actual
entire finite part of the literal completed tripling zero-fiber. The inverse
comes from the proved all-Scheme universal property, with both inverse
identities checked explicitly. -/
@[expose] def iso : ThreeTorsionScheme318.scheme A B hD ≅ fiber N where
  hom := toFiber N
  inv := fromFiber N
  hom_inv_id := by
    haveI:=ThreeTorsionClosed318.inclusion_closed A B hD
    apply (cancel_mono (ThreeTorsionScheme318.inclusion A B hD)).mp
    simp only [Category.assoc,fromFiber_inclusion,toFiber_fst,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,toFiber_fst,fromFiber_inclusion,Category.id_comp]
    · simp only [Category.assoc,toFiber_snd,fromFiber_base,Category.id_comp]
end LiteralFiniteKernelFiber318
