module
public import FourRootAffineChangeHolomorphy318
public import PELOriginalCompletedContactBiholomorph318
public import PELOriginalOrderedLegendreInvariants318
public import LiteralMetricExtension318
public section
noncomputable section
namespace PELOriginalLiteralContactScaling318
open Set FourRootNormalizedPointCharts318
open PELOriginalCommonContactBase318 PELOriginalManuscriptNormalization318
open PELOriginalCompletedContactBiholomorph318 LiteralMetricExtension318
open PELUnlevelledComplexBase318
open scoped Topology Manifold ContDiff
local instance : TopologicalSpace (Completed branches) := FourRootGluedTopology318.topology branches
local instance : TopologicalSpace (Completed contacts) := FourRootGluedTopology318.topology contacts
local instance : ChartedSpace ℂ (Completed branches) := FourRootCompletedComplexAtlas318.chartedSpace branches branches_injective
local instance : ChartedSpace ℂ (Completed contacts) := FourRootCompletedComplexAtlas318.chartedSpace contacts contacts_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed branches) := FourRootCompletedComplexAtlas318.complex_manifold branches branches_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed contacts) := FourRootCompletedComplexAtlas318.complex_manifold contacts contacts_injective
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

@[expose] def rootScale : ℂ := (Real.sqrt 32 : ℝ)
lemma rootScale_square : rootScale^2=32 := by
  change ((Real.sqrt 32 : ℝ) : ℂ)^2=(32:ℂ)
  exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤32)
lemma rootScale_ne : rootScale≠0 := by
  intro hz
  have hh := rootScale_square
  rw [hz] at hh
  norm_num at hh

variable (hλ : lambda=2401) (hμ : mu= -343/32)
include hλ hμ in
lemma branches_scaled (i : Fin 4) : contacts i=0+rootScale^2*branches i := by
  rw [rootScale_square]
  fin_cases i <;> norm_num [contacts,branches,hλ,hμ]

/-- The literal t↦32t comparison of the WHOLE completed curves, including
all original signed roots and eight infinity points. Numerical branch
identification is explicitly retained, not inferred from compactness. -/
@[expose] def scaling : Completed branches ≃ₜ Completed contacts :=
  FourRootAffineChangeCompletion318.homeomorph branches contacts 0 rootScale rootScale_ne
    (branches_scaled hλ hμ)
@[expose] def literalComparison : UnlevelledBase ≃ₜ Completed contacts := comparison.trans (scaling hλ hμ)

lemma forward_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (literalComparison hλ hμ) :=
  (FourRootAffineChangeHolomorphy318.holomorphic branches contacts branches_injective
    contacts_injective 0 rootScale rootScale_ne (branches_scaled hλ hμ)).comp
      PELOriginalCompletedContactBiholomorph318.forward_holomorphic
lemma inverse_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (literalComparison hλ hμ).symm :=
  PELOriginalCompletedContactBiholomorph318.inverse_holomorphic.comp
    (FourRootAffineChangeHolomorphy318.inverse_holomorphic branches contacts branches_injective
      contacts_injective 0 rootScale rootScale_ne (branches_scaled hλ hμ))

lemma marked_finite (p : FinitePoints branches) :
    literalComparison hλ hμ (comparison.symm (.inl p)) = .inl
      (FourRootAffineChangeCoordinates318.finiteForward branches contacts 0 rootScale
        (branches_scaled hλ hμ) p) := by
  change scaling hλ hμ (comparison (comparison.symm (.inl p)))=_
  rw [comparison.apply_symm_apply]
  rfl
lemma marked_base (p : FinitePoints branches) :
    (FourRootAffineChangeCoordinates318.finiteForward branches contacts 0 rootScale
      (branches_scaled hλ hμ) p).val.1=32*p.val.1 := by
  change 0+rootScale^2*p.val.1=32*p.val.1
  rw [zero_add,rootScale_square]
lemma marked_roots (p : FinitePoints branches) (i : Fin 4) :
    (FourRootAffineChangeCoordinates318.finiteForward branches contacts 0 rootScale
      (branches_scaled hλ hμ) p).val.2 i=rootScale*p.val.2 i := rfl
lemma marked_infinity (s : InfinitySigns) :
    literalComparison hλ hμ (comparison.symm (.inr s))=.inr s := by
  change scaling hλ hμ (comparison (comparison.symm (.inr s)))=_
  rw [comparison.apply_symm_apply]
  rfl

include hλ hμ in
/-- Compactness of the literal numerical completed curve comes from the
actual whole original source through this fixed comparison. -/
theorem literal_compact : CompactSpace (Completed contacts) := by
  apply isCompact_univ_iff.mp
  rw [←Set.range_eq_univ.mpr (literalComparison hλ hμ).surjective,←Set.image_univ]
  exact isCompact_univ.image (literalComparison hλ hμ).continuous

/-- The four missing geometric invariant identifications are the ONLY
numerical premises in this consumer. This theorem does not produce them. -/
theorem exists_of_published_invariants
    (h30 : PELOriginalOrderedLegendreInvariants318.invariant 3=
      (ContactCoordinates318.quarticJ (-43) (-686) (-2915) (-1372) (-172):ℂ))
    (h42 : PELOriginalOrderedLegendreInvariants318.invariant 2=
      (ContactCoordinates318.quarticJ (-43) 600 (-986) (-600) (-43):ℂ))
    (h70 : PELOriginalOrderedLegendreInvariants318.invariant 1=
      (ContactCoordinates318.quarticJ (-43) 256 (-130) (-768) (-387):ℂ))
    (h105 : PELOriginalOrderedLegendreInvariants318.invariant 0=
      (ContactCoordinates318.quarticJ (-43) 2 505 12 (-1548):ℂ)) :
    ∃ H : UnlevelledBase ≃ₜ Completed contacts,
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      (∀ s : InfinitySigns,H (comparison.symm (.inr s))=.inr s) := by
  obtain ⟨hl,hm⟩ := PELOriginalOrderedLegendreInvariants318.manuscript_parameters_of_published_invariants
    h30 h42 h70 h105
  exact ⟨literalComparison hl hm,forward_holomorphic hl hm,inverse_holomorphic hl hm,
    marked_infinity hl hm⟩
end PELOriginalLiteralContactScaling318
