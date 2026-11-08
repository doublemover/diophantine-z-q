module
public import LinearRootCoordinate318
public import ThreeRootOrder318
public section
noncomputable section
namespace FiniteBranchChart318
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 256
open Polynomial QuadraticPresentation318 LinearRootCoordinate318
open scoped TensorProduct
variable {F:Type*} [Field F] (c:Fˣ) (a:F) (d:Fin 3→Fˣ) (b:Fin 3→F)
abbrev Base:=F[X]
abbrev BranchBase:=LinearRootCoordinate318.Root c a
@[expose] def other (i:Fin 3) : Base (F:=F) := parameter (d i) (b i)
@[expose] def denominator : BranchBase c a :=
  ∏i:Fin 3,algebraMap (Base (F:=F)) (BranchBase c a) (other d b i)
abbrev OpenBase:=Localization.Away (denominator c a d b)
abbrev OriginalOrder:=BranchBase c a⊗[Base (F:=F)]ThreeRootOrder318.Order (other d b)
abbrev OpenOrder:=ThreeRootOrder318.Order
  (fun i=>algebraMap (Base (F:=F)) (OpenBase c a d b) (other d b i))

theorem denominator_at_branch :
    branchEvaluation c a (denominator c a d b)=∏i:Fin 3,(d i:F)*(a-b i) := by
  simp only [denominator,map_prod,other,branchEvaluation_other]

theorem denominator_at_branch_ne_zero (hb:∀i,a≠b i) :
    branchEvaluation c a (denominator c a d b)≠0 := by
  rw [denominator_at_branch]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>mul_ne_zero (d i).ne_zero (sub_ne_zero.mpr (hb i)))

theorem denominator_ne_zero (hb:∀i,a≠b i) : denominator c a d b≠0 := by
  intro h
  exact denominator_at_branch_ne_zero c a d b hb (by rw [h,map_zero])

/-- The branch point really belongs to this open neighborhood, via an
actual evaluation map on its localization. -/
@[expose] def branchPoint (hb:∀i,a≠b i) : OpenBase c a d b→+*F :=
  IsLocalization.Away.lift (denominator c a d b)
    (IsUnit.mk0 _ (denominator_at_branch_ne_zero c a d b hb))

@[simp] theorem branchPoint_on_base (hb:∀i,a≠b i) (z:BranchBase c a) :
    branchPoint c a d b hb (algebraMap (BranchBase c a) (OpenBase c a d b) z)=
      branchEvaluation c a z :=
  IsLocalization.Away.lift_eq _ _ _

theorem branchBase_domain : IsDomain (BranchBase c a) :=
  Function.Injective.isDomain (coordinateEquiv c a).toRingHom (coordinateEquiv c a).injective

theorem openBase_domain (hb:∀i,a≠b i) : IsDomain (OpenBase c a d b) := by
  letI:IsDomain (BranchBase c a):=branchBase_domain c a
  exact Localization.Away.isDomain (denominator_ne_zero c a d b hb)

theorem other_unit (i:Fin 3) :
    IsUnit (algebraMap (Base (F:=F)) (OpenBase c a d b) (other d b i)) := by
  rw [IsScalarTower.algebraMap_apply (Base (F:=F)) (BranchBase c a) (OpenBase c a d b)]
  apply IsLocalization.Away.isUnit_of_dvd (denominator c a d b)
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem two_unit (h2:(2:F)≠0) : IsUnit (2:OpenBase c a d b) := by
  simpa only [map_ofNat] using
    (IsUnit.mk0 (2:F) h2).map (algebraMap F (OpenBase c a d b))

local instance originalOrder_commRing : CommRing (OriginalOrder c a d b) := inferInstance
local instance originalOrder_algebra : Algebra (BranchBase c a) (OriginalOrder c a d b) := inferInstance
/-- The full original four-root order, now viewed over its genuine ramified
root coordinate, has this explicit localized three-root presentation. -/
@[expose] def localizedOrderEquiv :
    OpenBase c a d b⊗[BranchBase c a]OriginalOrder c a d b≃ₐ[OpenBase c a d b]
      OpenOrder c a d b :=
  (Algebra.TensorProduct.cancelBaseChange (Base (F:=F)) (BranchBase c a)
    (OpenBase c a d b) (OpenBase c a d b) (ThreeRootOrder318.Order (other d b))).trans
      (ThreeRootOrder318.baseChange (other d b) (OpenBase c a d b))

theorem open_finite_free_etale (h2:(2:F)≠0) :
    Module.Finite (OpenBase c a d b) (OpenOrder c a d b) ∧
    Module.Free (OpenBase c a d b) (OpenOrder c a d b) ∧
    Algebra.Etale (OpenBase c a d b) (OpenOrder c a d b) :=
  ⟨(ThreeRootOrder318.finite_free _).1,(ThreeRootOrder318.finite_free _).2,
    ThreeRootOrder318.etale _ (two_unit c a d b h2) (other_unit c a d b)⟩

theorem open_rank_eight (hb:∀i,a≠b i) :
    Module.finrank (OpenBase c a d b) (OpenOrder c a d b)=8 := by
  letI:IsDomain (OpenBase c a d b):=openBase_domain c a d b hb
  exact ThreeRootOrder318.rank_eight _

theorem open_faithfullyFlat (hb:∀i,a≠b i) :
    Module.FaithfullyFlat (OpenBase c a d b) (OpenOrder c a d b) := by
  letI:IsDomain (OpenBase c a d b):=openBase_domain c a d b hb
  exact ThreeRootOrder318.faithfullyFlat _
end FiniteBranchChart318

namespace FiniteBranchChart318
open Polynomial QuadraticPresentation318 LinearRootCoordinate318
variable {F:Type*} [Field F] (c:Fˣ) (a:F) (d:Fin 3→Fˣ) (b:Fin 3→F)

@[expose] def openRoot : OpenBase c a d b :=
  algebraMap (BranchBase c a) (OpenBase c a d b)
    (AdjoinRoot.root (polynomial (parameter c a)))

theorem open_contact_square :
    algebraMap (Base (F:=F)) (OpenBase c a d b) (X-C a)=
      algebraMap F (OpenBase c a d b) (↑(c⁻¹):F)*openRoot c a d b^2 := by
  rw [IsScalarTower.algebraMap_apply (Base (F:=F)) (BranchBase c a) (OpenBase c a d b),
    contact_square,map_mul,map_pow]
  rw [←IsScalarTower.algebraMap_apply F (BranchBase c a) (OpenBase c a d b)]
  rfl

@[simp] theorem branchPoint_root (hb:∀i,a≠b i) :
    branchPoint c a d b hb (openRoot c a d b)=0 := by
  rw [openRoot,branchPoint_on_base,branchEvaluation_root]
end FiniteBranchChart318
