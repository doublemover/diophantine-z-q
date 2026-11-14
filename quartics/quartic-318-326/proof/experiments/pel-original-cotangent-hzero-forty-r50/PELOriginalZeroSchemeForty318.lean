module
public import PELOriginalZeroSchemeSupport318
public import FourRootZeroGlobalSectionPoints318
public import ReducedClosedPointLift318
public section
noncomputable section
namespace PELOriginalZeroSchemeForty318
open AlgebraicGeometry CategoryTheory
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open FourRootGluedDerivativeIdeal318 FourRootCompletedSchemePoints318
open FourRootZeroGlobalSectionPoints318 PELOriginalZeroSchemeSupport318
local instance zeroReduced : IsReduced (zeroScheme branches) :=
  FourRootDerivativeZeroReduced318.reduced branches branches_injective
local instance pointQC (g : Spec (CommRingCat.of ℂ) ⟶ FourRootGluedScheme318.scheme branches) :
    QuasiCompact g := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
lemma self_base : Spec.algebraMap ℂ ℂ = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  change Spec.map (𝟙 (CommRingCat.of ℂ)) = _
  exact Spec.map_id _
/-- Composition by the existing closed immersion retains the actual
complex structural action. -/
@[expose] def toWhole (q : Points branches) : SchemePoints branches :=
  ⟨q.val ≫ into branches,by
    rw [Category.assoc]
    exact q.property.trans self_base.symm⟩
@[expose] def toSource (q : Points branches) : PELOriginalFiniteRamification318.Ramification := by
  refine ⟨PELOriginalContactSchemePoints318.comparison.symm (toWhole q),?_⟩
  apply (support_iff _).mp
  unfold InZero
  rw [Equiv.apply_symm_apply]
  exact ⟨q.val default,rfl⟩
lemma toSource_injective : Function.Injective toSource := by
  intro p q h
  have he : toWhole p = toWhole q :=
    PELOriginalContactSchemePoints318.comparison.symm.injective (congrArg Subtype.val h)
  apply Subtype.ext
  exact (cancel_mono (into branches)).mp (congrArg Subtype.val he)
/-- Every ORIGINAL ramification point lifts to the SAME reduced closed
zero scheme as an actual morphism, not merely a set-theoretic point. -/
lemma toSource_surjective : Function.Surjective toSource := by
  intro p
  let g := PELOriginalContactSchemePoints318.comparison p.val
  have hr : Set.range g.val ⊆ Set.range (into branches) := by
    rintro _ ⟨x,rfl⟩
    rw [Subsingleton.elim x default]
    exact (support_iff p.val).mpr p.property
  let q : Points branches :=
    ⟨ReducedClosedPointLift318.lift (into branches) g.val hr,by
      change ReducedClosedPointLift318.lift (into branches) g.val hr ≫
        (into branches ≫ FourRootGluedScheme318.structureMap branches) = _
      rw [←Category.assoc,ReducedClosedPointLift318.lift_fac]
      exact g.property.trans self_base⟩
  refine ⟨q,?_⟩
  apply Subtype.ext
  apply PELOriginalContactSchemePoints318.comparison.injective
  change PELOriginalContactSchemePoints318.comparison
    (PELOriginalContactSchemePoints318.comparison.symm (toWhole q)) = _
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact ReducedClosedPointLift318.lift_fac (into branches) g.val hr
/-- Exact entire original zero-scheme points, once each, correspond to
all original ramification points. No auxiliary count labels are used. -/
@[expose] def pointEquiv : Points branches ≃ PELOriginalFiniteRamification318.Ramification :=
  Equiv.ofBijective toSource ⟨toSource_injective,toSource_surjective⟩
theorem point_card_forty : Nat.card (Points branches) = 40 := by
  rw [Nat.card_congr pointEquiv,Nat.card_eq_fintype_card]
  exact PELOriginalDirectBranchEnumeration318.actual_branch_and_ramification_counts.2
/-- Genuine H0(O_Z), with its original structural scalar action, has
complex dimension40. This is not yet a theorem about H0 of Ω. -/
theorem global_sections_dimension_forty :
    Module.finrank ℂ (FourRootDerivativeZeroSections318.H0 branches) = 40 := by
  rw [←FourRootZeroGlobalSectionPoints318.card_eq_finrank branches branches_injective]
  exact point_card_forty
end PELOriginalZeroSchemeForty318
