module
public import IntegralCotangentTensor318
public import FractionSourceSections318
public section
noncomputable section
namespace VerticalCotangentSections318
open scoped TensorProduct
open IntegralCotangentTensor318
set_option maxHeartbeats 400000
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]
  (e : KaehlerDifferential R B ≃ₗ[B] B)

/-- Literal J²(dt tensor dt)/P(t), in the actual generic cotangent tensor
square rather than an independently defined coefficient. -/
@[expose] def q0 (t : K) : KaehlerDifferential R K ⊗[K] KaehlerDifferential R K :=
  ((VerticalSection318.J : K)^2 / VerticalSection318.denominator t) •
    ((KaehlerDifferential.D R K t) ⊗ₜ[K] (KaehlerDifferential.D R K t))
@[expose] def q1 (t : K) : KaehlerDifferential R K ⊗[K] KaehlerDifferential R K :=
  t • q0 (R := R) t

theorem q0_coefficient (t : K) :
    squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e) (q0 t) =
      VerticalSection318.section0 (FractionSourceSections318.derived e) t := by
  rw [q0, map_smul, squareFrame_pure]
  have hd : FractionKaehlerFrame318.genericFrame (K := K) e (KaehlerDifferential.D R K t) =
      FractionSourceSections318.derived e t :=
    Derivation.liftKaehlerDifferential_comp_D _ t
  rw [hd]
  simp only [VerticalSection318.section0, smul_eq_mul, pow_two]
  ring

theorem q1_coefficient (t : K) :
    squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e) (q1 t) =
      VerticalSection318.section1 (FractionSourceSections318.derived e) t := by
  rw [q1, map_smul, q0_coefficient]
  rfl

/-- Actual integral cotangent tensors map to the literal generic sections.
The integral differential frame and reduced-prime DVR condition are still
required geometric inputs; neither is inferred from a finite etale point cover. -/
theorem integral_sections [IsDiscreteValuationRing B] (p : ℕ)
    (hp : Irreducible (p : B)) (t : K) :
    (∃ x0, IntegralCotangentTensor318.map e x0 = q0 (R := R) t) ∧
    (∃ x1, IntegralCotangentTensor318.map e x1 = q1 (R := R) t) := by
  obtain ⟨h0, h1⟩ := FractionSourceSections318.vertical_sections e p hp t
  constructor
  · apply (integral_iff e (q0 t)).mpr
    rwa [q0_coefficient]
  · apply (integral_iff e (q1 t)).mpr
    rwa [q1_coefficient]

end VerticalCotangentSections318
