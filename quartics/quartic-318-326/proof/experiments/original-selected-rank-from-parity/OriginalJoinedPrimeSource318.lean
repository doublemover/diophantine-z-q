module
public import JacobiIndexPreparation318
public import AllScalarDetectorJoin318
public import ActualAnchorTwoConics318
public import PreparedIntegerSource318
public section
noncomputable section
namespace OriginalJoinedPrimeSource318
open CircuitReplay ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open GaussianQuarterModuli318 ActualCyclicClosure318 GeneratorScalarProgression318
open PreparedIntegerSource318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The paper's preparation-zero sufficient conditions, not an assertion of a point. -/
def Ready (b : ℚ) : Prop :=
  0<b ∧ b<17 ∧ IsSquare b.den ∧
    IsSquare (b:ℚ_[2]) ∧ 3≤padicValRat 2 b ∧
    IsSquare (b:ℚ_[3]) ∧ 1≤padicValRat 3 b ∧
    IsSquare (b:ℚ_[17]) ∧ 2≤padicValRat 17 b

/-- All exact Gaussian-pattern requests, after the continuity, size and
divisibility thresholds have been fixed. No unordered CM count or pole
point is included in this structure. -/
structure Pattern {labels : Fin 4 → ℤ} (C : Clearing labels) (L Q : ℕ) (T : ℚ) where
  u : ℤ
  w : ℤ
  values : Values C u w
  divisible : (Q:ℤ)∣w
  ray408 : ∀ k∈coefficients C, (408:ℤ)∣value u w k-1
  large : ∀ j : Fin 3, ∀ i : Fin 5, FixedSelectedPrimeBound318.bound C<(row C u w j i).natAbs
  A : Fin 3 × Fin 5 → ℤ
  B : Fin 3 × Fin 5 → ℤ
  gaussian : ∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (A i) (B i)
  a7 : ∀ i, A i%7=1
  b7 : ∀ i, B i%7=3
  pair : ∀ i j, Nat.gcd (GaussianNeighborNorms318.minus (A i) (B i))
    (GaussianNeighborNorms318.plus (A j) (B j))=4
  avoid : ∀ i, Avoid L (A i) (B i)
  cutoff : ∀ k∈coefficients C, L<(value u w k).natAbs
  E : ℝ
  errorBound : ∀ i, 1+2*|(A i:ℝ)|≤E
  spacing : E<(w:ℝ)^2
  band : ∀ k∈coefficients C, ∀ i : Fin 3 × Fin 5,
    ((row C u w i.1 i.2).natAbs:ℝ)+E<2*((value u w k).natAbs:ℝ)
  threshold : T≤parameter C u w

/-- Sufficient local conditions packaged identically for all four literal slots. -/
theorem scalarReady (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ)
    (hp : AllScalarSupportPreparation318.Prepared a labels h)
    (hr : 0<scalarB (a:ℚ) labels h ∧ scalarB (a:ℚ) labels h<17) :
    Ready (scalarB (a:ℚ) labels h) := by
  rcases hp with ⟨hs,hd,_⟩
  rcases hs with ⟨_,_,_,_,h2,h3,h17,s2,s3,s17⟩
  exact ⟨hr.1,hr.2,hd,s2,h2.ge.trans' (by decide),s3,h3.ge.trans' (by decide),
    s17,h17.ge⟩

/-- Exact universal forward projection conditional on three independent paper
inputs. The selected h is used directly, not reselected from an existential
family. The four calls to the point theorem can choose independent amplitudes. -/
theorem current_source
    (hpattern : ∀ (labels : Fin 4 → ℤ), (∀ j, labels j≠0) →
      ∀ (C : Clearing labels) (L Q : ℕ) (T : ℚ), 64∣L → 0<L → 0<Q →
        Nonempty (Pattern C L Q T))
    (hpoint : ∀ b : ℚ, Ready b → Nonempty (NormalizedPolePoints318.PointPair b))
    (hanchor : ∀ m : ℤ, m%24=1 → Nonempty (ActualAnchorTwoConics318.Pair m))
    (a : ℤ) : HasSolution (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ) := by
  classical
  obtain ⟨J,hJ,hprepare⟩ :=
    AllScalarDetectorJoin318.integer_preparation a 0 0 (2^16) 1 (by decide)
  have hd : J*1≠0 := mul_ne_zero (Nat.ne_of_gt hJ) one_ne_zero
  let d' := PreparedAnchorLabels318.multiplier (2^16) (J*1)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) _ hd
  let labels := FixedArithmeticLabels318.labels a 0 0 d' hd'
  have hn : ∀ j, labels j≠0 := FixedArithmeticLabels318.labels_nonzero _ _ _ _ _
  have hn1 : labels 1≠1 := by
    change ScalarPreparedResidues318.scalarLabel 0 0 d'≠1
    have hbound := (ScalarPreparedResidues318.label_domains 0 0 d' hd').1
    omega
  have hrels := FixedArithmeticLabels318.detector_relations a 0 0 d' hd'
  obtain ⟨h₀,L,N₂,N₃,N₁₇,_,_,hL,_,h64L,h64h,hscalar,h₂,h₃,h₁₇⟩ :=
    hprepare 1 one_ne_zero 0
  let C := ClearedContactForms318.construct labels
  obtain ⟨T,Q,hQ,hfamily⟩ := JacobiIndexPreparation318.prepared_family C
    (Current318FinalPolynomial.scale:ℚ) a hn hrels.1 hrels.2 h₀ L hL h64L h64h
    N₂ N₃ N₁₇ h₂ h₃ h₁₇
  obtain ⟨P⟩ := hpattern labels hn C L Q T h64L hL hQ
  obtain ⟨_,h,_,_,_,_,hcong,hreal,hguards,hdet,_,hrows,hbs,_,_⟩ :=
    hfamily P.u P.w P.values P.divisible P.ray408 P.large P.A P.B P.gaussian P.a7 P.b7
      P.pair P.avoid P.cutoff P.E P.errorBound P.spacing P.band P.threshold 0
  let t := parameter C P.u P.w
  let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t
  have hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0 := by
    intro j
    exact_mod_cast (abs_pos.mp (lt_trans (margin_positive labels hn j) (hguards j)))
  have readyDet : ∀ j : Fin 3, Ready (pre (190+51*j.val)) := hdet
  obtain ⟨P₀⟩ := hpoint (pre 190) (readyDet 0)
  obtain ⟨P₁⟩ := hpoint (pre 241) (readyDet 1)
  obtain ⟨P₂⟩ := hpoint (pre 292) (readyDet 2)
  obtain ⟨P₃⟩ := hpoint _ (scalarReady a labels h (hscalar h hcong)
    (scalar_domain a labels hn hn1 (h:ℤ) hreal))
  have hhom := ActualAnchorTwoConics318.actual hanchor a 0 0 (2^16) (J*1) hd
  exact complete_at_index (Current318FinalPolynomial.scale:ℚ) a labels hn hn1 (h:ℤ) t
    hg hreal hrows (fun j => (hbs j).1) P₀ P₁ P₂ P₃
    (PhysicalAnchorFromHomogeneous318.currentAnchor labels hhom)

end OriginalJoinedPrimeSource318
