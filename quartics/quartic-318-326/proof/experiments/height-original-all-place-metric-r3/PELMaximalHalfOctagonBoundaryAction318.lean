module
public import PELMaximalHalfOctagonOriginalPoints318
public import PELMaximalHalfOctagonBoundary318
public import PELPositiveNormalizerKlein318
public import PELFixedCandidateConjugators318
public section
noncomputable section
namespace PELMaximalHalfOctagonBoundaryAction318
open Set
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELPositiveNormalizerKlein318 PELFixedCandidateConjugators318 PELFixedCandidateWords318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonShape318 PELMaximalHalfOctagonBoundary318
open PELNormalizerOctagonAffine318
set_option maxHeartbeats 3000000

/-- Exact value, including the negative scalar of the original chronological
word. The action below cancels this scalar rather than replacing the word. -/
theorem vertical_value : ((conjugator 18).val:B)=(-1:ℚ) • embed ![7,1,0,-2] := by
  rw [conjugator,positiveWord_value,coordinate_certificate]
  ext <;> norm_num [wordScale,smallConjugator,embed]

theorem slant_value : ((conjugator 23).val:B)=(1:ℚ) • embed ![15,3,0,-5] := by
  rw [conjugator,positiveWord_value,coordinate_certificate]
  norm_num [wordScale,smallConjugator]

/-- The original central inertia rotates the entire actual Klein plane;
this is not restricted to the boundary or to rational points. -/
theorem center_action (τ : HalfPlane) :
    (scaledFirst (baseAction (inertiaElement 4) τ),scaledSecond (baseAction (inertiaElement 4) τ))=
      (-scaledFirst τ,-scaledSecond τ) := by
  apply original_coordinates_of_rows (inertiaElement 4) 1 (by norm_num) ![0,1,0,0]
  · norm_num [inertiaElement,PELInertiaNormalizerData318.rationalUnit,
      PELInertiaNormalizerData318.element,PELInertiaNormalizerData318.coefficients]
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed] <;> ring
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed] <;> ring

theorem top_action (τ : HalfPlane) (h : scaledSecond τ=1) :
    (scaledFirst (baseAction (inertiaElement 1) τ),scaledSecond (baseAction (inertiaElement 1) τ))=
      (-scaledFirst τ,scaledSecond τ) := by
  apply original_coordinates_of_rows (inertiaElement 1) 1 (by norm_num) ![0,1,0,-1]
  · norm_num [inertiaElement,PELInertiaNormalizerData318.rationalUnit,
      PELInertiaNormalizerData318.element,PELInertiaNormalizerData318.coefficients]
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,h] <;> ring
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,h]

theorem vertical_action (τ : HalfPlane) (h : scaledFirst τ=30) :
    (scaledFirst (baseAction (conjugator 18) τ),scaledSecond (baseAction (conjugator 18) τ))=
      (-scaledFirst τ,scaledSecond τ) := by
  apply original_coordinates_of_rows (conjugator 18) (-1) (by norm_num) ![7,1,0,-2] vertical_value
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,h]
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,h] <;> ring

theorem slant_action (τ : HalfPlane) (h : scaledFirst τ+7*scaledSecond τ=35) :
    (scaledFirst (baseAction (conjugator 23) τ),scaledSecond (baseAction (conjugator 23) τ))=
      (-scaledFirst τ,scaledSecond τ) := by
  apply original_coordinates_of_rows (conjugator 23) 1 (by norm_num) ![15,3,0,-5] slant_value
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed]
    nlinarith [congrArg (fun t : ℝ => scaledFirst τ*t) h]
  · norm_num [realRow,PELQuaternionKleinAction318.matrix,embed]
    nlinarith [congrArg (fun t : ℝ => scaledSecond τ*t) h]

@[expose] def reflectedCut (P : upperCut) : upperCut :=
  ⟨(-P.val.1,P.val.2),(upperCut_reflection P.val).mpr P.property⟩

theorem reflectedCut_involutive (P : upperCut) : reflectedCut (reflectedCut P)=P := by
  apply Subtype.ext
  simp [reflectedCut]

theorem reflected_center (P : upperCut) :
    (upperCutCenter (reflectedCut P)).val=ReflectedDiskJoukowski318.reflected (upperCutCenter P).val :=
  center_reflection P.val

/-- Turning a concrete row certificate into an equality of the actual
original half-plane points uses the established injective scaled chart. -/
theorem action_reflected (g : positiveNormalizer) (P : upperCut)
    (h : (scaledFirst (baseAction g (cutPoint P)),scaledSecond (baseAction g (cutPoint P)))=
      (-P.val.1,P.val.2)) : baseAction g (cutPoint P)=cutPoint (reflectedCut P) := by
  apply PELActualOriginalSideGluing318.scaled_injective
  rw [h,cutPoint_coordinates]
  rfl

theorem inverse_action_reflected (g : positiveNormalizer) (P : upperCut)
    (h : baseAction g (cutPoint (reflectedCut P))=cutPoint P) :
    baseAction g⁻¹ (cutPoint P)=cutPoint (reflectedCut P) := by
  rw [←h,←baseAction_mul,inv_mul_cancel,baseAction_one]

/-- Every literal boundary fold is produced by a genuine original
positive normalizer. Left sides use inverse words, not an assumed symmetry
of the orbit equivalence. Endpoints are included. -/
theorem boundary_original_action (P : upperCut)
    (hP : (upperCutCenter P).val∈frontier centeredPolygon) :
    ∃g : positiveNormalizer,baseAction g (cutPoint P)=cutPoint (reflectedCut P) := by
  have hc := cutPoint_coordinates P
  have hr := cutPoint_coordinates (reflectedCut P)
  have hA := congrArg Prod.fst hc
  have hB := congrArg Prod.snd hc
  have hrA := congrArg Prod.fst hr
  have hrB := congrArg Prod.snd hr
  change scaledFirst (cutPoint (reflectedCut P))= -P.val.1 at hrA
  change scaledSecond (cutPoint (reflectedCut P))=P.val.2 at hrB
  rcases (cut_boundary_iff P).mp hP with h | h | h | h | h | h
  · refine ⟨inertiaElement 4,action_reflected _ P ?_⟩
    rw [center_action,hA,hB,h,neg_zero]
  · refine ⟨inertiaElement 1,action_reflected _ P ?_⟩
    rw [top_action _ (by rw [hB,h]),hA,hB]
  · refine ⟨(conjugator 18)⁻¹,inverse_action_reflected _ P ?_⟩
    have hh := action_reflected (conjugator 18) (reflectedCut P) (by
      rw [vertical_action _ (by rw [hrA,h]; norm_num),hrA,hrB]
      rfl)
    simpa only [reflectedCut_involutive] using hh
  · refine ⟨conjugator 18,action_reflected _ P ?_⟩
    rw [vertical_action _ (by rw [hA,h]),hA,hB]
  · refine ⟨conjugator 23,action_reflected _ P ?_⟩
    rw [slant_action _ (by rw [hA,hB]; exact h),hA,hB]
  · refine ⟨(conjugator 23)⁻¹,inverse_action_reflected _ P ?_⟩
    have hh := action_reflected (conjugator 23) (reflectedCut P) (by
      rw [slant_action _ (by rw [hrA,hrB]; exact h),hrA,hrB]
      rfl)
    simpa only [reflectedCut_involutive] using hh

/-- Every full original arithmetic orbit meets the upper cut. First use
whole-group minimization, then the actual order-two center inertia. -/
theorem every_original_orbit_meets_cut (τ : HalfPlane) :
    ∃g : positiveNormalizer,(scaledFirst (baseAction g τ),scaledSecond (baseAction g τ))∈upperCut := by
  obtain ⟨g,hg⟩ := PELNormalizerOctagonReduction318.every_original_orbit_meets_octagon τ
  obtain ⟨hb0,hb1,ha0,ha1,hs0,hs1,ht0,ht1⟩ := hg
  by_cases h : 0≤scaledSecond (baseAction g τ)
  · refine ⟨g,h,hb1,ha0,ha1,hs1,?_⟩
    linarith
  · refine ⟨inertiaElement 4*g,?_⟩
    rw [baseAction_mul]
    have hc := center_action (baseAction g τ)
    change (scaledFirst (baseAction (inertiaElement 4) (baseAction g τ)),
      scaledSecond (baseAction (inertiaElement 4) (baseAction g τ)))∈upperCut
    rw [hc]
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem cutProjection_surjective : Function.Surjective cutProjection := by
  intro q
  obtain ⟨τ,rfl⟩ := maximalProjection_surjective q
  obtain ⟨g,hg⟩ := every_original_orbit_meets_cut τ
  refine ⟨⟨(scaledFirst (baseAction g τ),scaledSecond (baseAction g τ)),hg⟩,?_⟩
  change maximalProjection (cutPoint _) = maximalProjection τ
  rw [cutPoint_recovers,maximalProjection_invariant]

theorem boundary_projection (P : upperCut)
    (hP : (upperCutCenter P).val∈frontier centeredPolygon) :
    cutProjection (reflectedCut P)=cutProjection P := by
  obtain ⟨g,hg⟩ := boundary_original_action P hP
  change maximalProjection (cutPoint (reflectedCut P))=maximalProjection (cutPoint P)
  rw [←hg,maximalProjection_invariant]
end PELMaximalHalfOctagonBoundaryAction318
