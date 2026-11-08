module
public import InfinityDiagonalDivisibility318
public import NegatedCoordinateFrameFunctor318
public import ContactFrameNormalization318
public section
noncomputable section
namespace InfinityDifferentialDivisibility318
open InfinityReciprocalAction318 InfinityOrderCoordinates318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
/-- The actual all-four source sign, with the canonical Q-linear structure. -/
@[expose] def sign:Order c→ₐ[ℚ]Order c:=
  { (InfinitySignCoordinates318.sign c (fun _=>true)).toRingHom with
    commutes':=RingHom.map_rat_algebraMap _ }
lemma coordinate_negated:sign c (coordinate c)= -coordinate c:=
  InfinitySignCoordinates318.on_coordinate c (fun _=>true)
lemma coordinate_normalized:ContactDifferentialFrames318.infinityFrame c
    (KaehlerDifferential.D ℚ (Order c) (coordinate c))=1:=
  ContactFrameNormalization318.infinity_coordinate_normalized c
/-- Invariance of an actual algebraic infinity differential forces its du
coefficient to be anti-invariant under the literal full sign. -/
theorem coefficient_anti (ω:KaehlerDifferential ℚ (Order c))
    (h:AlgHomDifferential318.map (sign c) ω=ω):
    InfinitySignCoordinates318.sign c (fun _=>true)
      (ContactDifferentialFrames318.infinityFrame c ω)=
        -ContactDifferentialFrames318.infinityFrame c ω:=
  NegatedCoordinateFrameFunctor318.fixed_coefficient
    (ContactDifferentialFrames318.infinityFrame c) (coordinate c) (coordinate_normalized c)
    (sign c) (coordinate_negated c) ω h
/-- The entire infinity chart, not only residue points: every invariant
regular differential has a du coefficient divisible by the actual u. -/
theorem fixed_divisible (ω:KaehlerDifferential ℚ (Order c))
    (h:AlgHomDifferential318.map (sign c) ω=ω):
    coordinate c ∣ ContactDifferentialFrames318.infinityFrame c ω:=
  InfinityDiagonalDivisibility318.divisible c _ (coefficient_anti c ω h)
/-- Actual regular factorization through u du, with no rational extension
or quotient reducedness assumption. -/
theorem fixed_factorization (ω:KaehlerDifferential ℚ (Order c))
    (h:AlgHomDifferential318.map (sign c) ω=ω):
    ∃a:Order c,ω=(coordinate c*a) • KaehlerDifferential.D ℚ (Order c) (coordinate c):=by
  obtain ⟨a,ha⟩:=fixed_divisible c ω h
  refine ⟨a,?_⟩
  apply (ContactDifferentialFrames318.infinityFrame c).injective
  rw [map_smul,coordinate_normalized,smul_eq_mul,mul_one]
  exact ha
end InfinityDifferentialDivisibility318
