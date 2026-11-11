module
public import PELActualOrderNormalizer318
public section
noncomputable section
namespace PELInertiaRationalConjugacy318
open PELQuaternionAlgebra318 PELQuaternionNormParity318 PELInertiaNormalizerData318
set_option maxHeartbeats 1000000

theorem parity_conjugation (u x : Bˣ) : parityHom (u*x*u⁻¹)=parityHom x := by
  simp only [map_mul,map_inv]
  simp [mul_comm,mul_left_comm,mul_assoc]

theorem scalar_parity (q : ℚˣ) : parityHom (scalarUnit q)=1 := parity_scalar q

theorem inertia_parity (i : Fin 5) :
    parityHom (PELInertiaNormalizerData318.rationalUnit i)=
      Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) :=
  PELActualOrderNormalizer318.parity_inertia i

/-- The five ORIGINAL inertia elements remain distinct under conjugation
by EVERY rational quaternion unit, even after arbitrary nonzero rational
rescaling. No normalizer membership or geometric orbit premise is needed. -/
theorem index_of_conjugate_scalar (i j : Fin 5) (u : Bˣ) (q : ℚˣ)
    (h : u*PELInertiaNormalizerData318.rationalUnit i*u⁻¹=
      scalarUnit q*PELInertiaNormalizerData318.rationalUnit j) : i=j := by
  have hp := congrArg parityHom h
  rw [parity_conjugation,map_mul,scalar_parity,one_mul,inertia_parity,inertia_parity] at hp
  exact InertiaLabels318.five_labels_injective (congrArg Multiplicative.toAdd hp)

theorem not_conjugate_scalar (i j : Fin 5) (hij : i≠j) (u : Bˣ) (q : ℚˣ) :
    u*PELInertiaNormalizerData318.rationalUnit i*u⁻¹≠
      scalarUnit q*PELInertiaNormalizerData318.rationalUnit j :=
  fun h => hij (index_of_conjugate_scalar i j u q h)

/-- Same obstruction on the literal quaternion elements, with the full
original conjugation and signed scalar multiplication retained. -/
theorem index_of_element_conjugacy (i j : Fin 5) (u : Bˣ) (q : ℚ) (hq : q≠0)
    (h : (u:B)*element i*(↑u⁻¹:B)=q • element j) : i=j := by
  apply index_of_conjugate_scalar i j u (Units.mk0 q hq)
  apply Units.ext
  change (u:B)*element i*(↑u⁻¹:B)=algebraMap ℚ B q*element j
  simpa only [Algebra.smul_def] using h
end PELInertiaRationalConjugacy318
