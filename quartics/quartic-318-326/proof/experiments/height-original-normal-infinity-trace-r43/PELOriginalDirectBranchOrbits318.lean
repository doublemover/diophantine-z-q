module
public import PELOriginalBranchFiniteRepresentatives318
public import PELFixedCandidateCoverage318
public section
noncomputable section
namespace PELOriginalDirectBranchOrbits318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicFixedParameter318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELIntegralEllipticObstructions318 PELLevelThreeSimilitudes318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELUnlevelledComplexBase318 PELUnlevelledNormalizerAction318
open PELInertiaArithmeticFixedPoints318 PELOriginalLabeledFixedOrbits318
open PELFixedCandidateConjugators318
set_option maxHeartbeats 2400000

/-- A nonzero lower-left real matrix coefficient makes its fixed point
in the original upper half-plane unique, by the actual real/imaginary equations. -/
theorem fixedLine_unique (M : RealMatrices) (hc : M 1 0≠0)
    (τ σ : HalfPlane) (hτ : fixesLine M τ) (hσ : fixesLine M σ) : τ=σ := by
  obtain ⟨ha,hb⟩ := coordinate_relations M τ τ.property hτ
  obtain ⟨ha',hb'⟩ := coordinate_relations M σ σ.property hσ
  have hr0 : M 1 0*((τ:ℂ).re-(σ:ℂ).re)=0 := by linarith
  have hr : (τ:ℂ).re=(σ:ℂ).re := sub_eq_zero.mp ((mul_eq_zero.mp hr0).resolve_left hc)
  have hi0 : M 1 0*((τ:ℂ).im^2-(σ:ℂ).im^2)=0 := by rw [hr] at hb; nlinarith only [hb,hb']
  have hi2 := (mul_eq_zero.mp hi0).resolve_left hc
  have hi : (τ:ℂ).im=(σ:ℂ).im := by nlinarith [τ.property,σ.property]
  apply Subtype.ext
  exact Complex.ext hr hi

/-- The original finite word carries the original inertia fixed point to
ANY upper-half-plane point fixed by that exact listed integral candidate. -/
theorem candidate_fixed_point (k : Fin 77) (τ : HalfPlane)
    (ht : trace (candidate k)=0)
    (hf : fixesLine (representation (embed (candidate k))) τ) :
    τ=baseAction (conjugator k) (originalFixedPoint (label k)) := by
  let g := conjugator k
  let n : positiveNormalizer := g*inertiaElement (label k)*g⁻¹
  have hn : (n.val:B)=embed (candidate k) := actual_conjugation k
  have hfixed : baseAction n (baseAction g (originalFixedPoint (label k)))=
      baseAction g (originalFixedPoint (label k)) := by
    rw [←baseAction_mul]
    have hmul : n*g=g*inertiaElement (label k) := by dsimp [n]; group
    rw [hmul,baseAction_mul,original_fixed]
  have hline : fixesLine (representation (embed (candidate k)))
      (baseAction g (originalFixedPoint (label k))) := by
    rw [←hn]
    exact fixesLine_of_mobius _ _
      (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive n) _
        (baseAction g (originalFixedPoint (label k))).property)
      (congrArg Subtype.val hfixed)
  have htrace : representation (embed (candidate k)) 0 0+
      representation (embed (candidate k)) 1 1=0 := by
    rw [PELPrincipalThreeStabilizer318.representation_trace,original_trace,ht]
    norm_num
  have hdet : 0<(representation (embed (candidate k))).det := by
    rw [←hn]
    exact matrix_positive n
  exact fixedLine_unique _
    (PELNontrivialFixedTraceZero318.positive_trace_zero_lower_left _ hdet htrace) τ _ hf hline

/-- COMPLETE actual original nontrivial stabilizer locus, without genus,
Euler, cellulation, Riemann-Hurwitz or an assumed branch enumeration. -/
theorem every_branch_original_orbit (x : UnlevelledBase)
    (v : InertiaLabels318.V) (hv : v≠0) (hx : Multiplicative.ofAdd v • x=x) :
    ∃ (i : Fin 5) (g : Multiplicative InertiaLabels318.V),g • originalPoint i=x := by
  obtain ⟨τ,a,i,hp,ht,hn,hr,hf,hrows⟩ :=
    PELOriginalBranchFiniteRepresentatives318.original_branch_representative x v hv hx
  obtain ⟨k,hki,hka⟩ := PELFixedCandidateCoverage318.original_candidate_covered i a ht hr hrows
  have ht' : trace (candidate k)=0 := by rwa [hka]
  have hf' : fixesLine (representation (embed (candidate k))) τ := by rwa [hka]
  have he := candidate_fixed_point k τ ht' hf'
  refine ⟨label k,PELPositiveOrderNormalizer318.parity (conjugator k),?_⟩
  rw [←PELFullNormalizerAction318.actual_action_factorization]
  change coarseAction (conjugator k) (projection (originalFixedPoint (label k)))=x
  rw [coarseAction_square,←he,hp]
end PELOriginalDirectBranchOrbits318
