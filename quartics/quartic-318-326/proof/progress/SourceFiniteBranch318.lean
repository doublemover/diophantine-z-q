module
public import FiniteBranchChart318
public import FourRootPivot318
public import ContactKummerOrder318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace SourceFiniteBranch318
open Polynomial
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open FourRootPivot318 LinearContactSquareclass318 FiniteBranchChart318
variable (c:Fin 4→ℚˣ) (i:Fin 4)
@[expose] def otherTwist (j:Fin 3) : ℚˣ := c (indices i j.succ)
@[expose] def otherContact (j:Fin 3) : ℚ := contacts (indices i j.succ)
abbrev BranchBase:=FiniteBranchChart318.BranchBase (c i) (contacts i)
abbrev OpenBase:=FiniteBranchChart318.OpenBase (c i) (contacts i) (otherTwist c i) (otherContact i)
abbrev OpenOrder:=FiniteBranchChart318.OpenOrder (c i) (contacts i) (otherTwist c i) (otherContact i)
abbrev RegroupedOrder:=FiniteBranchChart318.OriginalOrder (c i) (contacts i) (otherTwist c i) (otherContact i)

theorem other_distinct : ∀j,contacts i≠otherContact i j := by
  intro j
  have h:indices i 0≠indices i j.succ := (indices_injective i).ne (by intro h; have hval:=congrArg Fin.val h; simp at hval)
  simpa only [indices_zero,otherContact] using contacts_injective.ne h

/-- A genuine identification with the original exact twisted Q[t]-order,
for each of the four possible branch points. -/
@[expose] def sourceRegroup :
    ContactKummerOrder318.SourceOrder c≃ₐ[ℚ[X]]RegroupedOrder c i :=
  Fin.cases (FourRootPivot318.regroup (ContactKummerOrder318.coefficient c) 0)
    (Fin.cases (FourRootPivot318.regroup (ContactKummerOrder318.coefficient c) 1)
      (Fin.cases (FourRootPivot318.regroup (ContactKummerOrder318.coefficient c) 2)
        (Fin.cases (FourRootPivot318.regroup (ContactKummerOrder318.coefficient c) 3)
          (fun j=>Fin.elim0 j)))) i

local instance regrouped_commRing : CommRing (RegroupedOrder c i) := inferInstance
local instance regrouped_algebra : Algebra (BranchBase c i) (RegroupedOrder c i) := inferInstance

@[expose] def localizedSourceEquiv :
    OpenBase c i⊗[BranchBase c i]RegroupedOrder c i≃ₐ[OpenBase c i]OpenOrder c i :=
  FiniteBranchChart318.localizedOrderEquiv (c i) (contacts i) (otherTwist c i) (otherContact i)

@[expose] def sourceBranchPoint : OpenBase c i→+*ℚ :=
  FiniteBranchChart318.branchPoint (c i) (contacts i) (otherTwist c i) (otherContact i)
    (other_distinct i)

/-- Exact finite-branch chart over Q, with no supplied distinctness, unit,
rank, etaleness, or nonemptiness hypothesis. All four twists remain arbitrary. -/
theorem source_finite_branch :
    Module.Finite (OpenBase c i) (OpenOrder c i) ∧
    Module.Free (OpenBase c i) (OpenOrder c i) ∧
    Algebra.Etale (OpenBase c i) (OpenOrder c i) ∧
    Module.finrank (OpenBase c i) (OpenOrder c i)=8 ∧
    Module.FaithfullyFlat (OpenBase c i) (OpenOrder c i) := by
  have h:=FiniteBranchChart318.open_finite_free_etale (c i) (contacts i)
    (otherTwist c i) (otherContact i) (by norm_num : (2:ℚ)≠0)
  exact ⟨h.1,h.2.1,h.2.2,FiniteBranchChart318.open_rank_eight _ _ _ _ (other_distinct i),
    FiniteBranchChart318.open_faithfullyFlat _ _ _ _ (other_distinct i)⟩

theorem source_contact_square :
    algebraMap ℚ[X] (OpenBase c i) (Polynomial.X-Polynomial.C (contacts i))=
      algebraMap ℚ (OpenBase c i) (↑((c i)⁻¹):ℚ)*
        FiniteBranchChart318.openRoot (c i) (contacts i) (otherTwist c i) (otherContact i)^2 :=
  FiniteBranchChart318.open_contact_square _ _ _ _
end SourceFiniteBranch318

namespace SourceFiniteBranch318
open Polynomial
open scoped TensorProduct
open FiniteBranchChart318
variable (c:Fin 4→ℚˣ) (i:Fin 4)

local instance regrouped_commRing2 : CommRing (RegroupedOrder c i) := inferInstance
local instance regrouped_algebra2 : Algebra (BranchBase c i) (RegroupedOrder c i) := inferInstance

theorem regrouped_domain : IsDomain (RegroupedOrder c i) := by
  letI:IsDomain (ContactKummerOrder318.SourceOrder c):=ContactKummerOrder318.source_domain c
  exact Function.Injective.isDomain (sourceRegroup c i).symm.toRingHom (sourceRegroup c i).symm.injective

theorem regrouped_free : Module.Free (BranchBase c i) (RegroupedOrder c i) := by
  letI:Module.Free ℚ[X] (ThreeRootOrder318.Order
    (FiniteBranchChart318.other (otherTwist c i) (otherContact i))):=
      (ThreeRootOrder318.finite_free _).2
  exact inferInstanceAs (Module.Free (BranchBase c i)
    (BranchBase c i⊗[ℚ[X]]ThreeRootOrder318.Order
      (FiniteBranchChart318.other (otherTwist c i) (otherContact i))))

/-- The branch-chart algebra is the entire localized original domain,
without selecting or assuming a component. -/
theorem source_chart_domain : IsDomain (OpenOrder c i) := by
  letI:IsDomain (RegroupedOrder c i):=regrouped_domain c i
  letI:Module.Free (BranchBase c i) (RegroupedOrder c i):=regrouped_free c i
  have hi:Function.Injective (algebraMap (BranchBase c i) (RegroupedOrder c i)):=
    FaithfulSMul.algebraMap_injective _ _
  let D:BranchBase c i:=FiniteBranchChart318.denominator (c i) (LinearContactSquareclass318.contacts i)
    (otherTwist c i) (otherContact i)
  have hd:algebraMap (BranchBase c i) (RegroupedOrder c i) D≠0 := by
    have hD:D≠0:=FiniteBranchChart318.denominator_ne_zero _ _ _ _ (other_distinct i)
    simpa only [map_zero] using hi.ne hD
  letI:IsLocalization.Away (algebraMap (BranchBase c i) (RegroupedOrder c i) D)
      (RegroupedOrder c i⊗[BranchBase c i]OpenBase c i) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (RegroupedOrder c i)
        (Submonoid.powers D)) (RegroupedOrder c i⊗[BranchBase c i]OpenBase c i))
  letI:IsDomain (RegroupedOrder c i⊗[BranchBase c i]OpenBase c i):=
    IsLocalization.Away.isDomain _ hd
  let e:OpenOrder c i≃+*(RegroupedOrder c i⊗[BranchBase c i]OpenBase c i):=
    (localizedSourceEquiv c i).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm (BranchBase c i) (OpenBase c i) (RegroupedOrder c i)).toRingEquiv
  exact Function.Injective.isDomain e e.injective
end SourceFiniteBranch318
