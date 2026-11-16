module
public import RealGuardWitness318
public import RealMultiples318
public import CompressedGeneratorBridge318
public section

/-! Exact arithmetic seam for the historical simultaneous real-guard choice.
This module does not equip the real point orbit with an analytic torus or prove
the dense-progression selection theorem. It identifies the guard and proves its
strictly positive value at the identity for every nonzero integer label. -/
namespace RealGuardTrace318
open ConcreteG8Domain (K pair)
open LocalGenerator318 (E P)
open CompressedGeneratorBridge318 (transport curve_eq)
open ActualQuadraticEmbeddings318
open WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
noncomputable section

/-- The source's rational real coefficient is half the sum of both embeddings. -/
theorem real_coefficient (x : K) :
    (x.re : ℝ)=(positiveEmbedding x+negativeEmbedding x)/2 := by
  rcases x with ⟨a,b⟩
  change (a:ℝ)=(positiveEmbedding (pair a b)+negativeEmbedding (pair a b))/2
  rw [positiveEmbedding,negativeEmbedding,realEmbedding_pair,realEmbedding_pair]
  ring

theorem coefficient_pos (x : K) (hp : 0<positiveEmbedding x)
    (hm : 0<negativeEmbedding x) : 0<x.re := by
  have h : (0:ℝ)<(x.re:ℝ) := by rw [real_coefficient]; positivity
  exact_mod_cast h

/-- Reciprocal abscissa, with the identity value exactly zero. -/
@[expose] def reciprocal (Q : E.Point) : K := (Q.xRep 1)/(Q.xRep 0)

@[simp] theorem reciprocal_zero : reciprocal 0=0 := by
  simp [reciprocal]

/-- Pullback of the actual reciprocal chart, including the identity case. -/
theorem reciprocal_chart (u v : K) (hc : v^2=1-CompressedOrientation318.D*u^4) :
    reciprocal (transport curve_eq (PrimaryFormal318.point u v
      (ReciprocalDifference318.ordinate_ne u v hc) hc))=u^2 := by
  by_cases hu : u=0
  · simp [hu,PrimaryFormal318.point]
  · simp [reciprocal,PrimaryFormal318.point,hu,CompressedGeneratorBridge318.transport_some,Point.xRep_some]

/-- The same rational real coefficient as the four literal source guards. -/
@[expose] def guardValue (n : ℤ) (H : E.Point) : ℚ :=
  (reciprocal (n • (H-P))-reciprocal (n • H)).re

/-- Exact identity consumed by any future simultaneous real-orbit selection. -/
theorem guard_eq_trace (n : ℤ) (H : E.Point) :
    (guardValue n H : ℝ)=
      ((positiveEmbedding (reciprocal (n • (H-P))) -
        positiveEmbedding (reciprocal (n • H))) +
       (negativeEmbedding (reciprocal (n • (H-P))) -
        negativeEmbedding (reciprocal (n • H))))/2 := by
  rw [guardValue,real_coefficient,map_sub,map_sub]

/-- Identification uses the actual oriented points, not their abscissae alone. -/
theorem literal_guard (u v : Fin 8 → K) (j : Fin 4) (n : ℤ) (H : E.Point)
    (hc : ∀ i, (v i)^2=1-CompressedOrientation318.D*(u i)^4)
    (hU : transport curve_eq (PrimaryFormal318.point (u (j.castAdd 4)) (v (j.castAdd 4))
      (ReciprocalDifference318.ordinate_ne _ _ (hc _)) (hc _)) = n • H)
    (hV : transport curve_eq (PrimaryFormal318.point (u (j.natAdd 4)) (v (j.natAdd 4))
      (ReciprocalDifference318.ordinate_ne _ _ (hc _)) (hc _)) = n • (H-P)) :
    (RealGuardWitness318.denominator u j).re=guardValue n H := by
  rw [guardValue,←hV,←hU,reciprocal_chart,reciprocal_chart]
  rfl

theorem reciprocal_multiple_positive (σ : K →+* ℝ) (n : ℤ) (hn : n≠0) :
    0<σ (reciprocal (n • P)) := by
  have hcoord : (n • P).xRep 1=1 := by
    cases he : n • P with
    | zero => exact False.elim ((RealMultiples318.multiple_P_nonzero n hn) he)
    | some x y h => simp [Point.xRep_some]
  rw [reciprocal,hcoord,map_div₀,map_one]
  exact one_div_pos.mpr (lt_trans zero_lt_one
    (RealMultiples318.multiple_P_abscissa_gt_one σ n hn))

/-- This gives the nonzero value used in the historical real-analytic argument.
It applies to every nonzero integer label, without assuming a source solution. -/
theorem guard_at_identity_positive (n : ℤ) (hn : n≠0) : 0<guardValue n 0 := by
  have he : n • ((0:E.Point)-P)=(-n) • P := by simp
  simp only [guardValue,he,zsmul_zero,reciprocal_zero,sub_zero]
  exact coefficient_pos _ (reciprocal_multiple_positive positiveEmbedding (-n) (neg_ne_zero.mpr hn))
    (reciprocal_multiple_positive negativeEmbedding (-n) (neg_ne_zero.mpr hn))

theorem guard_not_identically_zero (n : ℤ) (hn : n≠0) :
    ¬(∀ H : E.Point, guardValue n H=0) := by
  intro h
  exact (ne_of_gt (guard_at_identity_positive n hn)) (h 0)

/-- The selected nonzero traces would provide exactly the four explicit guards
required by first51_rows, with no weakening to K-nonvanishing. -/
theorem guards_of_actual_points (u v : Fin 8 → K) (n : Fin 4 → ℤ) (H : E.Point)
    (hc : ∀ i, (v i)^2=1-CompressedOrientation318.D*(u i)^4)
    (hU : ∀ j : Fin 4, transport curve_eq (PrimaryFormal318.point (u (j.castAdd 4)) (v (j.castAdd 4))
      (ReciprocalDifference318.ordinate_ne _ _ (hc _)) (hc _)) = n j • H)
    (hV : ∀ j : Fin 4, transport curve_eq (PrimaryFormal318.point (u (j.natAdd 4)) (v (j.natAdd 4))
      (ReciprocalDifference318.ordinate_ne _ _ (hc _)) (hc _)) = n j • (H-P))
    (hg : ∀ j : Fin 4, guardValue (n j) H≠0) : RealGuardWitness318.Guards u := by
  intro j
  rw [literal_guard u v j (n j) H hc (hU j) (hV j)]
  exact hg j

#print axioms real_coefficient
#print axioms reciprocal_chart
#print axioms literal_guard
#print axioms guard_at_identity_positive
#print axioms guards_of_actual_points
end
end RealGuardTrace318
