module
public import ActualLocalAnchorWitness318
public import AnchorAnisotropy
public import Current326Bridge
public section
noncomputable section
namespace PhysicalAnchorFromHomogeneous318
open FixedDetectorScales318 ActualAnchorRatio318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Exact remaining rational local-global producer. The affine denominator
is not assumed nonzero; the retained rational anisotropy theorem proves it. -/
@[expose] def Homogeneous (ns : Fin 4 → ℤ) (N : ℕ) : Prop :=
  ∃ X Y Z T : ℚ, (¬(X=0 ∧ Y=0 ∧ Z=0 ∧ T=0)) ∧
    X^2+6*Y^2-2*Z^2=(3*(ratio ns N)^2-2)*T^2

theorem exists_anchor (ns : Fin 4 → ℤ) (N : ℕ) (h : Homogeneous ns N) :
    Nonempty (ScalarCompleteSource318.Anchor ((3:ℚ)^N) (normProduct ns)
      (ActualScalarRoot318.inverseNorm (ns 1))) := by
  obtain ⟨x,y,z,he⟩ := AnchorAnisotropy.rational_representation_of_homogeneous
    (3*(ratio ns N)^2-2) h
  refine ⟨⟨(3:ℚ)^N*x,(3:ℚ)^N*y,(3:ℚ)^N*z,?_⟩⟩
  rw [physical_identity ns N]
  linear_combination ((3:ℚ)^N)^2*he

noncomputable def anchor (ns : Fin 4 → ℤ) (N : ℕ) (h : Homogeneous ns N) :
    ScalarCompleteSource318.Anchor ((3:ℚ)^N) (normProduct ns)
      (ActualScalarRoot318.inverseNorm (ns 1)) := Classical.choice (exists_anchor ns N h)

noncomputable def currentAnchor (ns : Fin 4 → ℤ) (h : Homogeneous ns (2^16)) :
    ScalarCompleteSource318.Anchor (Current318FinalPolynomial.scale:ℚ) (normProduct ns)
      (ActualScalarRoot318.inverseNorm (ns 1)) := by
  rw [Current326Bridge.scale_cast]
  exact anchor ns (2^16) h

/-- Exceptional local physical-anchor equations at the literal current scale. -/
@[expose] def CurrentLocalAnchors (ns : Fin 4 → ℤ) : Prop :=
  (∃ x : ℚ_[2], x^2=
    3*(4096*(normProduct ns:ℚ_[2])*((Current318FinalPolynomial.scale:ℚ):ℚ_[2])+
      (ActualScalarRoot318.inverseNorm (ns 1):ℚ_[2]))^2-
      2*((Current318FinalPolynomial.scale:ℚ):ℚ_[2])^2) ∧
  (∃ x : ℚ_[3], x^2=
    3*(4096*(normProduct ns:ℚ_[3])*((Current318FinalPolynomial.scale:ℚ):ℚ_[3])+
      (ActualScalarRoot318.inverseNorm (ns 1):ℚ_[3]))^2-
      2*((Current318FinalPolynomial.scale:ℚ):ℚ_[3])^2)

/-- Genuine2/3 Hensel witnesses at the exact final scale on the same labels. -/
theorem actual_current_locals (a : ℤ) (A B d : ℕ) (hd : d≠0) :
    CurrentLocalAnchors (FixedArithmeticLabels318.labels a A B
      (PreparedAnchorLabels318.multiplier (2^16) d)
      (PreparedAnchorLabels318.multiplier_ne (2^16) d hd)) := by
  unfold CurrentLocalAnchors
  rw [Current326Bridge.scale_cast]
  simpa only [Rat.cast_pow,Rat.cast_ofNat] using
    ActualLocalAnchorWitness318.actual_local_anchors a A B (2^16) d hd

end PhysicalAnchorFromHomogeneous318
