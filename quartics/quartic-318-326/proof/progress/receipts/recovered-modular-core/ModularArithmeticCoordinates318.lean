module
public import ThreeArithmeticFinite318
public import ThirdArithmeticHolomorphic318
public import Mathlib.Topology.LocalAtTarget
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ModularArithmeticCoordinates318
open OpenJModel318 OpenJAffineScheme318 OpenJComplexEvaluation318
open ThreeArithmeticPoint318 ThreeArithmeticQuotient318 CanonicalXModularity318
set_option maxHeartbeats 0

@[expose] def xGenerator (N : ℕ) [NeZero N] : LiteralThreeXComparison318.Fixed N :=
  ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial (A N) (B N)))

lemma fixedPoint_x (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    fixedPoint N tau h (xGenerator N)=arithmeticX tau := by
  change point N tau h ((ThreeTorsionSignQuotient318.signQuotientEquiv
    (A N) (B N) (discriminant_unit N)).symm
      ((ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)) _))=_
  rw [AlgEquiv.symm_apply_apply,point_root]

/-- The actual j and x generators separate all complex points of the literal fixed algebra. -/
theorem hom_ext (N : ℕ) [NeZero N]
    (f g : LiteralThreeXComparison318.Fixed N →+* ℂ)
    (hj : f (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N))=
      g (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N)))
    (hx : f (xGenerator N)=g (xGenerator N)) : f=g := by
  let e := ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)
  have hb : f.comp (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N))=
      g.comp (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator N))
    apply Polynomial.ringHom_ext
    · intro n
      simp
    · exact hj
  have he : f.comp e.toRingEquiv.toRingHom=g.comp e.toRingEquiv.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · rw [←AdjoinRoot.algebraMap_eq]
      apply RingHom.ext
      intro r
      change f (e (algebraMap (Base N) _ r))=g (e (algebraMap (Base N) _ r))
      rw [e.commutes]
      exact RingHom.congr_fun hb r
    · exact hx
  apply RingHom.ext
  intro r
  obtain ⟨s,rfl⟩ := e.surjective r
  exact RingHom.congr_fun he s

@[expose] def sourceX (q : Source) : ℂ := arithmeticX (representative q)

lemma complexPoint_x (N : ℕ) [NeZero N] (q : Source) :
    complexPoint N q (xGenerator N)=sourceX q :=
  fixedPoint_x N (representative q) (representative_admissible q)

lemma sourceX_projection (tau : UpperHalfPlane) (h : Admissible tau) :
    sourceX (projection tau h)=arithmeticX tau := by
  rw [←complexPoint_x 1,complexPoint_projection,fixedPoint_x]

abbrev Locus := {tau : UpperHalfPlane // Admissible tau}
@[expose] def sourceProjection (tau : Locus) : Source := projection tau.val tau.property

lemma sourceProjection_surjective : Function.Surjective sourceProjection := by
  intro q
  refine ⟨⟨representative q,representative_admissible q⟩,?_⟩
  exact Subtype.ext (representative_projection q)

lemma sourceProjection_isOpenQuotientMap : IsOpenQuotientMap sourceProjection := by
  have h : IsOpenQuotientMap (GammaOneAtlas318.quotientMap 3) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact h.restrictPreimage {q | QuotientJ318.jMap 3 q≠0 ∧ QuotientJ318.jMap 3 q≠1728}

lemma periodX_continuous : Continuous (fun tau : Locus => arithmeticX tau.val) := by
  apply continuous_iff_continuousAt.mpr
  intro tau
  have ha := ThirdArithmeticHolomorphic318.arithmeticX_analyticAt tau.val tau.property
  have hc : ContinuousAt (fun b : Locus => (b.val:ℂ)) tau := by fun_prop
  have hh := ha.continuousAt.comp (f := fun b : Locus => (b.val:ℂ)) hc
  simpa only [Function.comp_def,UpperHalfPlane.ofComplex_apply] using hh

/-- Continuity descends through the actual open orbit quotient, retaining stabilizers. -/
theorem sourceX_continuous : Continuous sourceX := by
  apply sourceProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def,sourceProjection,sourceX_projection] using periodX_continuous

@[expose] def coordinates (q : Source) : ℂ × ℂ := (QuotientJ318.jMap 3 q.val,sourceX q)

lemma coordinates_continuous : Continuous coordinates :=
  ((ActualJAllLevels318.continuous_j 3).comp continuous_subtype_val).prodMk sourceX_continuous

/-- Both actual arithmetic coordinate functions are holomorphic on the period locus. -/
theorem period_coordinates_holomorphic (tau : UpperHalfPlane) (h : Admissible tau) :
    AnalyticAt ℂ (fun z => (ActualQJ318.jInvariant (UpperHalfPlane.ofComplex z),
      arithmeticX (UpperHalfPlane.ofComplex z))) (tau:ℂ) :=
  (OpenJLocalComparison318.j_analyticAt tau).prod
    (ThirdArithmeticHolomorphic318.arithmeticX_analyticAt tau h)

end ModularArithmeticCoordinates318
