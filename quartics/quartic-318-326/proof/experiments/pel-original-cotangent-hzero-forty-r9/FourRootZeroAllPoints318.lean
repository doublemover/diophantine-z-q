module
public import PELOriginalZeroSchemeForty318
public import Mathlib.AlgebraicGeometry.Artinian
public section
noncomputable section
namespace FourRootZeroAllPoints318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318 FourRootZeroGlobalSectionPoints318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
local instance finite : IsFinite (FourRootDerivativeZeroFinite318.structure b) :=
  FourRootDerivativeZeroFinite318.finite b hb
local instance locallyArtinian : IsLocallyArtinian (zeroScheme b) :=
  IsLocallyArtinian.of_locallyQuasiFinite (FourRootDerivativeZeroFinite318.structure b)
/-- EVERY scheme point of the original finite zero scheme is closed.
This is not restricted to the already-known complex-valued points. -/
lemma point_closed (x : zeroScheme b) : IsClosed ({x} : Set (zeroScheme b)) := isClosed_singleton
@[expose] def closedEquiv : closedPoints (zeroScheme b) ≃ zeroScheme b where
  toFun := Subtype.val
  invFun x := ⟨x,point_closed b hb x⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- The actual residue-field construction realizes EVERY topological
point as its unique base-preserving complex-valued scheme point. -/
@[expose] def underlyingEquiv : Points b ≃ zeroScheme b :=
  (pointEquivClosedPoint (FourRootDerivativeZeroFinite318.structure b)).trans (closedEquiv b hb)
lemma underlyingEquiv_apply (p : Points b) : underlyingEquiv b hb p = p.val default := by
  change p.val (IsLocalRing.closedPoint ℂ) = p.val default
  exact congrArg p.val (Subsingleton.elim _ _)
end FourRootZeroAllPoints318

namespace PELOriginalZeroAllPoints318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 FourRootGluedDerivativeIdeal318
@[expose] def originalEquiv : zeroScheme branches ≃ PELOriginalFiniteRamification318.Ramification :=
  (FourRootZeroAllPoints318.underlyingEquiv branches branches_injective).symm.trans
    PELOriginalZeroSchemeForty318.pointEquiv
/-- The original labels preserve the existing closed immersion point,
not only the cardinality of an abstract finite set. -/
lemma originalEquiv_point (z : zeroScheme branches) :
    (PELOriginalContactSchemePoints318.comparison (originalEquiv z).val).val default =
      into branches z := by
  change (PELOriginalContactSchemePoints318.comparison
    (PELOriginalContactSchemePoints318.comparison.symm
      (PELOriginalZeroSchemeForty318.toWhole
        ((FourRootZeroAllPoints318.underlyingEquiv branches branches_injective).symm z)))).val default = _
  rw [Equiv.apply_symm_apply]
  change into branches
    (((FourRootZeroAllPoints318.underlyingEquiv branches branches_injective).symm z).val default) = _
  rw [←FourRootZeroAllPoints318.underlyingEquiv_apply,Equiv.apply_symm_apply]
instance finite : Finite (zeroScheme branches) := Finite.of_equiv _ originalEquiv.symm
theorem card_forty : Nat.card (zeroScheme branches) = 40 := by
  rw [Nat.card_congr originalEquiv,Nat.card_eq_fintype_card]
  exact PELOriginalDirectBranchEnumeration318.actual_branch_and_ramification_counts.2
end PELOriginalZeroAllPoints318
