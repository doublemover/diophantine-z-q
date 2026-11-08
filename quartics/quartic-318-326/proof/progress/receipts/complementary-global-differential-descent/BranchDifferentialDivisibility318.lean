module
public import BranchFlipQuotient318
public import NegatedCoordinateFrameFunctor318
public section
noncomputable section
namespace BranchDifferentialDivisibility318
open AlgebraicGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) (i:Fin 4)
abbrev B:=ContactIntrinsicFrames318.BranchRing c i
abbrev t:B c i:=ContactFrameNormalization318.sourceCoordinate c i
abbrev sign:B c i→ₐ[ℚ]B c i:=(BranchSignLocalization318.flip c i).toAlgHom
lemma coordinate_normalized:ContactDifferentialFrames318.sourceLocalizationFrame c i
    (KaehlerDifferential.D ℚ (B c i) (t c i))=1:=
  ContactFrameNormalization318.source_coordinate_normalized c i
lemma coefficient_anti (ω:KaehlerDifferential ℚ (B c i))
    (h:AlgHomDifferential318.map (sign c i) ω=ω):
    BranchSignLocalization318.flip c i (ContactDifferentialFrames318.sourceLocalizationFrame c i ω)=
      -ContactDifferentialFrames318.sourceLocalizationFrame c i ω:=
  NegatedCoordinateFrameFunctor318.fixed_coefficient
    (ContactDifferentialFrames318.sourceLocalizationFrame c i) (t c i) (coordinate_normalized c i)
    (sign c i) (BranchSignLocalization318.flip_coordinate c i) ω h
/-- Actual whole-ring divisibility of the dy_i coefficient; no residue-only
or reduced-quotient argument is substituted. -/
theorem fixed_divisible (ω:KaehlerDifferential ℚ (B c i))
    (h:AlgHomDifferential318.map (sign c i) ω=ω):
    t c i∣ContactDifferentialFrames318.sourceLocalizationFrame c i ω:=
  BranchFlipQuotient318.divisible c i _ (coefficient_anti c i ω h)
/-- A fixed regular differential is a regular multiple of y_i dy_i on the
entire omitted finite branch, including its ramification divisor. -/
theorem fixed_factorization (ω:KaehlerDifferential ℚ (B c i))
    (h:AlgHomDifferential318.map (sign c i) ω=ω):
    ∃a:B c i,ω=(t c i*a) • KaehlerDifferential.D ℚ (B c i) (t c i):=by
  obtain ⟨a,ha⟩:=fixed_divisible c i ω h
  refine ⟨a,?_⟩
  apply (ContactDifferentialFrames318.sourceLocalizationFrame c i).injective
  rw [map_smul,coordinate_normalized,smul_eq_mul,mul_one]
  exact ha
end BranchDifferentialDivisibility318
