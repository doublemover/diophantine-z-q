module
public import DyadicNormalizedRatioCharts318
public import DyadicRationalRepresentative318
public section
noncomputable section
namespace DyadicRationalNormalizedContacts318
open scoped TensorProduct
open DyadicFourRatioMarkedOrder318 DyadicNormalizedRatioCharts318 DyadicRationalRepresentative318
variable {R : Type*} [CommRing R] (K : Type*) [Field K] [CharZero K] [Algebra R K]
variable (q : Fin 4 → ℚ) (l : Fin 4 → R)

/-- Clearing a rational coefficient uses the square of its denominator. -/
@[expose] def cleared (i : Fin 4) : R := (((q i).num * ((q i).den:ℤ) : ℤ) : R) * l i

theorem original_relation (i : Fin 4) :
    (q i : K) * algebraMap R K (l i) = algebraMap R K (cleared q l i) * ((q i).den:K)⁻¹^2 := by
  have hd : ((q i).den:K)≠0 := Nat.cast_ne_zero.mpr (q i).den_ne_zero
  simp only [cleared,map_mul,map_intCast,Int.cast_mul,Int.cast_natCast,Rat.cast_def]
  field_simp <;> ring

/-- The genuine generic four-root algebra with the given rational coefficients
is identified with the ambient algebra used to normalize the integral chart. -/
@[expose] def originalGenericEquiv :
    FourRootOrder318.Order (fun i => (q i : K) * algebraMap R K (l i)) ≃ₐ[K]
      Ambient K (cleared q l) := by
  let e (i : Fin 4) := UnitRootScaling318.equiv _ _
    (Units.mk0 ((q i).den:K) (Nat.cast_ne_zero.mpr (q i).den_ne_zero))⁻¹
    (original_relation K q l i)
  exact (Algebra.TensorProduct.congr (Algebra.TensorProduct.congr (e 0) (e 1))
    (Algebra.TensorProduct.congr (e 2) (e 3))).trans (FourRootOrder318.baseChange (cleared q l) K).symm

/-- The coefficient base can be a local ring over 2 and R its polynomial
or reciprocal-parameter chart. Only integer units 1 mod 4 are needed in R. -/
theorem normalized_representative (hq : ∀ i, q i≠0)
    (hunit : ∀ u : ℤ, IsUnit (1+4*(u:R))) :
    ∃ r c : Fin 4 → ℤ, (∀ i, Rep (r i)) ∧
      (∀ i, IsUnit (1+4*(c i:R))) ∧
      Nonempty (Joint (fun i => (c i:R)) ⊗[R] integralClosure R (Ambient K (cleared q l)) ≃ₐ[Joint (fun i => (c i:R))]
        Joint (fun i => (c i:R)) ⊗[R] integralClosure R (Ambient K (fun i => (r i:R)*l i))) := by
  have H (i : Fin 4) := integer_decomposition ((q i).num*((q i).den:ℤ))
    (mul_ne_zero (Rat.num_ne_zero.mpr (hq i)) (Nat.cast_ne_zero.mpr (q i).den_ne_zero))
  choose r c j hr he using H
  let v (i : Fin 4) : Kˣ := Units.mk0 ((2:K)^j i) (pow_ne_zero _ (by norm_num))
  let a (i : Fin 4) : R := ((r i:R)*l i)*(1+4*(c i:R))
  refine ⟨r,c,hr,fun i => hunit _,⟨comparison K (fun i => (c i:R)) (fun i => hunit _)
    (cleared q l) a (fun i => (r i:R)*l i) v ?_ (fun _ => rfl)⟩⟩
  intro i
  have hm : (cleared q l i) = a i * ((2:R)^j i)^2 := by
    unfold cleared a
    rw [he i]
    push_cast
    ring
  rw [hm,map_mul,map_pow,map_pow,map_ofNat] <;> rfl

theorem units_from_local_base {A : Type*} [CommRing A] [IsLocalRing A] [Algebra A R]
    (h2 : (2:A) ∈ IsLocalRing.maximalIdeal A) (u : ℤ) : IsUnit (1+4*(u:R)) := by
  simpa only [map_add,map_one,map_mul,map_ofNat,map_intCast] using
    (residual_unit h2 (u:A)).map (algebraMap A R)

end DyadicRationalNormalizedContacts318
