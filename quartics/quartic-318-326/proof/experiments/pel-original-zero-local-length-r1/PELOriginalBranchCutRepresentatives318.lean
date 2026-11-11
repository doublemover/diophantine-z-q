module
public import PELOriginalMarkedSphere318
public import PELOriginalFixedIntegralCoordinates318
public import PELMaximalHalfOctagonBoundaryAction318
public import PELOriginalCompactConformalCore318
public section
noncomputable section
namespace PELOriginalBranchCutRepresentatives318
open Set
open QuaternionicJointPeriodTopology318 QuaternionicFixedParameter318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELInertiaArithmeticFixedPoints318 PELFixedCandidateConjugators318
open PELIntegralEllipticObstructions318 PELLevelThreeSimilitudes318
open PELOriginalFixedIntegralCoordinates318 PELDirichletHeight318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonShape318 PELMaximalHalfOctagonBoundary318
open PELOriginalMarkedSphere318 PELStabilizerLocusInvariant318
set_option maxHeartbeats 3000000

/-- Exact rows of the independently classified ORIGINAL integral normalizers.
The index order is the fixed inertia order30,42,70,105,210. -/
@[expose] def row : Fin 5→Fin 77:=![4,14,28,41,44]
@[expose] def position : Fin 5→ℝ×ℝ:=![(30,0),(0,1),(28,1),(30,5/7),(0,0)]
lemma row_label (i:Fin 5) : label (row i)=i := by
  fin_cases i <;> norm_num [row,label]
lemma position_mem (i:Fin 5) : position i∈upperCut := by
  fin_cases i <;> norm_num [position,upperCut]
@[expose] def representative (i:Fin 5) : upperCut:=⟨position i,position_mem i⟩

/-- Conjugation transports the actual fixed line, not only the norm or label. -/
lemma candidate_line (k:Fin 77) :
    fixesLine (representation (embed (candidate k)))
      (baseAction (conjugator k) (originalFixedPoint (label k))) := by
  let g:=conjugator k
  let n:positiveNormalizer:=g*inertiaElement (label k)*g⁻¹
  have hn:(n.val:B)=embed (candidate k):=actual_conjugation k
  have hfixed:baseAction n (baseAction g (originalFixedPoint (label k)))=
      baseAction g (originalFixedPoint (label k)) := by
    rw [←baseAction_mul]
    have hmul:n*g=g*inertiaElement (label k):=by dsimp [n]; group
    rw [hmul,baseAction_mul,original_fixed]
  rw [←hn]
  exact fixesLine_of_mobius _ _
    (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive n) _
      (baseAction g (originalFixedPoint (label k))).property)
    (congrArg Subtype.val hfixed)

lemma row_coordinates (i:Fin 5) :
    (scaledFirst (baseAction (conjugator (row i)) (originalFixedPoint i)),
      scaledSecond (baseAction (conjugator (row i)) (originalFixedPoint i)))=position i := by
  have ht:trace (candidate (row i))=0:=by
    fin_cases i <;> norm_num [row,candidate,trace]
  have hn:0<integralNorm (candidate (row i)):=by
    fin_cases i <;> norm_num [row,candidate,integralNorm]
  have hf:=candidate_line (row i)
  rw [row_label] at hf
  obtain ⟨_,hA,hB,_⟩:=original_fixed_coordinates (candidate (row i)) ht hn _ hf
  apply Prod.ext
  · rw [hA]
    fin_cases i <;> norm_num [row,candidate,rotationCoordinate,position]
  · rw [hB]
    fin_cases i <;> norm_num [row,candidate,rotationCoordinate,position]

/-- Each displayed cut point is the actual original orbit representative,
not a rational Klein point silently substituted for a complex branch value. -/
theorem actual_representative (i:Fin 5) :
    cutPoint (representative i)=baseAction (conjugator (row i)) (originalFixedPoint i) := by
  apply PELActualOriginalSideGluing318.scaled_injective
  rw [cutPoint_coordinates,row_coordinates]
  rfl

theorem projection_representative (i:Fin 5) :
    cutProjection (representative i)=branchPoint i := by
  change maximalProjection (cutPoint (representative i))=branchPoint i
  rw [actual_representative,maximalProjection_invariant]
  rfl

theorem representative_boundary (i:Fin 5) :
    (upperCutCenter (representative i)).val∈frontier centeredPolygon := by
  rw [cut_boundary_iff]
  fin_cases i <;> norm_num [representative,position]

/-- The ENTIRE original branch image is realized on the genuine cut boundary.
This is stronger than locating five unrelated candidate points. -/
theorem branch_boundary (q:PELOriginalMaximalQuotient318.MaximalBase) (hq:q∈branchImage) :
    ∃P:upperCut,cutProjection P=q ∧
      (upperCutCenter P).val∈frontier centeredPolygon := by
  rw [branchImage_eq_range] at hq
  obtain ⟨i,rfl⟩:=hq
  exact ⟨representative i,projection_representative i,representative_boundary i⟩

/-- No actual branch image is hidden in the original strict conformal interior. -/
theorem branch_not_interior (q:PELOriginalMaximalQuotient318.MaximalBase)
    (hq:q∈branchImage) : q∉PELOriginalOpenDenseInterior318.originalInterior := by
  obtain ⟨P,rfl,hP⟩:=branch_boundary q hq
  apply PELOriginalCompactConformalCore318.boundary_not_originalInterior P
  rw [←interior_eq_strict]
  exact fun hi=>hP.2 hi
end PELOriginalBranchCutRepresentatives318
