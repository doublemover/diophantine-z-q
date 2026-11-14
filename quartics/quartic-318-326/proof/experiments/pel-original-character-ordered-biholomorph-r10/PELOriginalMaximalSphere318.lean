module
public import PELMaximalHalfOctagonBoundaryAction318
public import PELNormalizerHalfCutOrbit318
public section
noncomputable section
namespace PELOriginalMaximalSphere318
open Set
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonShape318 PELMaximalHalfOctagonSphere318
open PELMaximalHalfOctagonBoundary318 PELMaximalHalfOctagonBoundaryAction318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open scoped OnePoint
set_option maxHeartbeats 3000000

/-- The all-normalizer equality classifier's intrinsic boundary condition
is the actual frontier of the cut polygon, not just the old octagon. -/
theorem nonstrict_cut_boundary (P : upperCut)
    (h : P.val.2=0 ∨ ¬PELNormalizerOctagonStrata318.strict P.val) :
    (upperCutCenter P).val∈frontier centeredPolygon := by
  by_contra hn
  have hn' := mt (cut_boundary_iff P).mpr hn
  simp only [not_or] at hn'
  obtain ⟨h0,h1,hA0,hA1,hS,hT⟩ := hn'
  obtain ⟨hb0,hb1,ha0,ha1,hs,ht⟩ := P.property
  have hb1' : P.val.2<1 := lt_of_le_of_ne hb1 h1
  have ha0' : -30<P.val.1 := lt_of_le_of_ne ha0 hA0.symm
  have ha1' : P.val.1<30 := lt_of_le_of_ne ha1 hA1
  have hs' : P.val.1+7*P.val.2<35 := lt_of_le_of_ne hs hS
  have ht' : -P.val.1+7*P.val.2<35 := lt_of_le_of_ne ht hT
  rcases h with h | h
  · exact h0 h
  · apply h
    exact ⟨by linarith,hb1',ha0',ha1',by linarith,hs',by linarith,by linarith⟩

/-- Exact equality criterion for the unchanged arithmetic projection from
the literal half-octagon. Both directions are produced independently:
whole-lattice no-hidden classification and four original normalizer words. -/
theorem cutProjection_fibers (P Q : upperCut) : cutProjection P=cutProjection Q ↔
    P=Q ∨ ((upperCutCenter P).val∈frontier centeredPolygon ∧ Q=reflectedCut P) := by
  constructor
  · intro he
    obtain ⟨g,hg⟩ := (maximalProjection_eq_iff (cutPoint Q) (cutPoint P)).mp he.symm
    have hcP := cutPoint_coordinates P
    have hcQ := cutPoint_coordinates Q
    have hAP := congrArg Prod.fst hcP
    have hBP := congrArg Prod.snd hcP
    have hAQ := congrArg Prod.fst hcQ
    have hBQ := congrArg Prod.snd hcQ
    have hP := cut_in_octagon P.val P.property
    have hQ := cut_in_octagon Q.val Q.property
    have h := PELNormalizerHalfCutOrbit318.no_hidden_halfcut_identifications g (cutPoint P)
      (by simpa only [hAP,hBP] using hP)
      (by rw [hg]; simpa only [hAQ,hBQ] using hQ)
      (by have := P.property.1; simpa only [hAP,hBP] using this)
      (by rw [hg]; have := Q.property.1; simpa only [hAQ,hBQ] using this)
    simp only [hg,hAP,hBP,hAQ,hBQ] at h
    rcases h with h | ⟨h,hb⟩
    · exact Or.inl (Subtype.ext h.symm)
    · right
      exact ⟨nonstrict_cut_boundary P hb,Subtype.ext h⟩
  · rintro (rfl | ⟨hb,rfl⟩)
    · rfl
    · exact (boundary_projection P hb).symm

@[expose] def centeredProjection (z : centeredPolygon) : PELOriginalMaximalQuotient318.MaximalBase :=
  cutProjection (upperCutCenter.symm z)

theorem centeredProjection_continuous : Continuous centeredProjection :=
  cutProjection_continuous.comp upperCutCenter.symm.continuous

theorem centeredProjection_surjective : Function.Surjective centeredProjection :=
  cutProjection_surjective.comp upperCutCenter.symm.surjective

/-- The literal geometric pairing and the ACTUAL full arithmetic orbit
fibers coincide. No quotient relation is defined using the desired sphere. -/
theorem centeredProjection_fibers (z w : centeredPolygon) :
    centeredProjection z=centeredProjection w ↔ z=w ∨ boundaryPair z w := by
  rw [centeredProjection,centeredProjection,cutProjection_fibers]
  constructor
  · rintro (he | ⟨hb,hw⟩)
    · exact Or.inl (upperCutCenter.symm.injective he)
    · right
      refine ⟨by simpa using hb,?_⟩
      have hc := congrArg (fun P : upperCut => (upperCutCenter P).val) hw
      simpa only [Homeomorph.apply_symm_apply,reflected_center] using hc
  · rintro (rfl | ⟨hb,hw⟩)
    · exact Or.inl rfl
    · right
      refine ⟨by simpa using hb,?_⟩
      apply upperCutCenter.injective
      apply Subtype.ext
      simpa only [Homeomorph.apply_symm_apply,reflected_center] using hw

theorem arithmetic_sphere_fibers (z w : centeredPolygon) :
    centeredProjection z=centeredProjection w ↔ sphereMap z=sphereMap w := by
  rw [centeredProjection_fibers,sphereMap_fibers]

theorem generated_respects_arithmetic (z w : centeredPolygon)
    (h : Relation.EqvGen boundaryPair z w) : centeredProjection z=centeredProjection w :=
  (arithmetic_sphere_fibers z w).mpr ((complete_generated_relation z w).mp h)

@[expose] def arithmeticComparison : PairedHalfOctagon → PELOriginalMaximalQuotient318.MaximalBase :=
  Quotient.lift centeredProjection generated_respects_arithmetic

theorem arithmeticComparison_continuous : Continuous arithmeticComparison :=
  centeredProjection_continuous.quotient_lift generated_respects_arithmetic

theorem arithmeticComparison_bijective : Function.Bijective arithmeticComparison := by
  constructor
  · intro a b hab
    obtain ⟨z,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨w,rfl⟩ := Quotient.mk_surjective b
    exact Quotient.sound ((complete_generated_relation z w).mpr
      ((arithmetic_sphere_fibers z w).mp hab))
  · intro q
    obtain ⟨z,hz⟩ := centeredProjection_surjective q
    exact ⟨Quotient.mk _ z,hz⟩

/-- Compact-to-Hausdorff quotient identification for the actual original
full normalizer. In particular no fundamental-domain assertion is supplied
as an input: coverage and complete fibers were constructed above. -/
@[expose] def actualHalfOctagon : PairedHalfOctagon ≃ₜ PELOriginalMaximalQuotient318.MaximalBase :=
  (Equiv.ofBijective arithmeticComparison arithmeticComparison_bijective).toHomeomorphOfContinuousClosed
    arithmeticComparison_continuous arithmeticComparison_continuous.isClosedMap

/-- The ACTUAL original maximal arithmetic quotient is a topological
sphere. This homeomorphism is not asserted to be holomorphic: the radial
gauge normalization is topological, and analytic P1/algebraization is a
separate remaining construction. -/
@[expose] def originalMaximalSphere : PELOriginalMaximalQuotient318.MaximalBase ≃ₜ OnePoint ℂ :=
  actualHalfOctagon.symm.trans pairedHalfOctagonSphere

theorem originalMaximalSphere_projection (z : centeredPolygon) :
    originalMaximalSphere (centeredProjection z)=sphereMap z := by
  change pairedHalfOctagonSphere (actualHalfOctagon.symm (actualHalfOctagon (Quotient.mk _ z)))=_
  rw [Homeomorph.symm_apply_apply]
  rfl
end PELOriginalMaximalSphere318
