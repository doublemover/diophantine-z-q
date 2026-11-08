module
public import LiteralKernelScalar318
public import ActualKernelBaseChange318
public import FiniteEtaleFieldPoints318
public import CartesianSectionPoints318
public section
noncomputable section
namespace LiteralKernelFieldCard318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (F:Type) [Field F] [IsAlgClosed F] [Algebra (OpenJModel318.Base N) F]
local notation "R"=>OpenJModel318.Base N
local notation "A"=>OpenJAffineScheme318.A N
local notation "B"=>OpenJAffineScheme318.B N
local notation "hD"=>OpenJAffineScheme318.discriminant_unit N
local notation "b"=>Spec.map (CommRingCat.ofHom (algebraMap R F))
local notation "C"=>KernelScalarExtension318.ring N F
local instance : Module.Finite F C:=KernelScalarExtension318.finite N F
local instance : Algebra.Etale F C:=KernelScalarExtension318.etale N F
lemma iso_hom_base : (ActualLiteralKernelBaseChange318.iso N F).hom ≫ Spec.algebraMap F C=
    ActualLiteralKernelBaseChange318.structureMap N F:=by
  rw [←ActualLiteralKernelBaseChange318.iso_inv_base,←Category.assoc,Iso.hom_inv_id,Category.id_comp]
/-- This equivalence uses the actual kernel pullback, then the actual
scalar-coordinate isomorphism; it does not assert it is additive. -/
@[expose] def pointEquiv : LiteralKernelSchemePoints318.Points N b ≃ FiniteEtaleFieldPoints318.Points F C:=
  (CartesianSectionPoints318.equiv (ActualKernelBaseChange318.isPullback (S:=F) A B hD)).symm.trans
    (CartesianSectionPoints318.isoEquiv (ActualLiteralKernelBaseChange318.iso N F)
      (ActualLiteralKernelBaseChange318.structureMap N F) (Spec.algebraMap F C) (iso_hom_base N F))
/-- Cardinality of the actual geometric kernel points. Its F3 addition is
the independently constructed represented group, not the scalar labels. -/
theorem card_nine [NeZero N] : Nat.card (LiteralKernelSchemePoints318.Points N b)=9:=by
  rw [Nat.card_congr (pointEquiv N F),FiniteEtaleFieldPoints318.card_points,KernelScalarExtension318.rank_nine]
end LiteralKernelFieldCard318
