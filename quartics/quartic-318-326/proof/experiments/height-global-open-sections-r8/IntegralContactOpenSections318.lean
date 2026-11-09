module
public import IntegralContactOpenFrame318
public section
noncomputable section
namespace IntegralContactOpenSections318
open IntegralContactOpenFrame318 Polynomial
open scoped TensorProduct
set_option maxHeartbeats 400000
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

@[expose] def poleProduct : Order R c :=
  algebraMap (Base R) (Order R c) (algebraMap R[X] (Base R) (denominator R))
@[expose] def inverseProduct : Order R c :=
  algebraMap (Base R) (Order R c) (IsLocalization.Away.invSelf (denominator R))

/-- The inverted element is exactly the original four-contact polynomial. -/
theorem poleProduct_literal : poleProduct R c =
    coordinate R c * (coordinate R c - 32) * (coordinate R c - 76832) *
      (coordinate R c + 343) := by
  have hd : denominator R = X*(X-32)*(X-76832)*(X+343) := by
    norm_num [denominator,contacts,Fin.prod_univ_four,map_ofNat]
  have hm := congrArg (fun q : R[X] => algebraMap (Base R) (Order R c)
    (algebraMap R[X] (Base R) q)) hd
  simpa only [poleProduct,map_mul,map_sub,map_add,map_ofNat,coordinate] using hm

theorem product_inverse : poleProduct R c * inverseProduct R c = 1 := by
  unfold poleProduct inverseProduct
  rw [←map_mul, IsLocalization.Away.mul_invSelf, map_one]

theorem inverse_product : inverseProduct R c * poleProduct R c = 1 := by
  rw [mul_comm, product_inverse]

/-- These are actual coefficients in the integral order, not numbers
asserted to belong to a chosen lattice after specialization. -/
@[expose] def coefficient0 : Order R c := (2765952000 : Order R c)^2 * inverseProduct R c
@[expose] def coefficient1 : Order R c := coordinate R c * coefficient0 R c

theorem coefficient0_cleared : coefficient0 R c * poleProduct R c = (2765952000 : Order R c)^2 := by
  rw [coefficient0, mul_assoc, inverse_product, mul_one]

@[expose] def q0 : KaehlerDifferential R (Order R c) ⊗[Order R c]
    KaehlerDifferential R (Order R c) :=
  coefficient0 R c • ((KaehlerDifferential.D R (Order R c) (coordinate R c)) ⊗ₜ[Order R c]
    (KaehlerDifferential.D R (Order R c) (coordinate R c)))
@[expose] def q1 : KaehlerDifferential R (Order R c) ⊗[Order R c]
    KaehlerDifferential R (Order R c) := coordinate R c • q0 R c

@[expose] def tensorFrame (h2 : IsUnit (2 : R)) :
    (KaehlerDifferential R (Order R c) ⊗[Order R c] KaehlerDifferential R (Order R c))
      ≃ₗ[Order R c] Order R c :=
  (TensorProduct.congr (frame R c h2) (frame R c h2)).trans (TensorProduct.lid _ _)

theorem q0_coefficient (h2 : IsUnit (2 : R)) :
    tensorFrame R c h2 (q0 R c) = coefficient0 R c := by
  rw [q0, map_smul]
  change coefficient0 R c *
    (frame R c h2 (KaehlerDifferential.D R (Order R c) (coordinate R c)) *
      frame R c h2 (KaehlerDifferential.D R (Order R c) (coordinate R c))) = _
  simp only [frame_D, one_mul, mul_one]

theorem q1_coefficient (h2 : IsUnit (2 : R)) :
    tensorFrame R c h2 (q1 R c) = coefficient1 R c := by
  rw [q1, map_smul, q0_coefficient]
  rfl

/-- The construction has the exact literal denominator after any ring map
into a field. The nonzero denominator is proved from the integral inverse. -/
theorem image_product_ne {K : Type*} [Field K] (f : Order R c →+* K) :
    f (poleProduct R c) ≠ 0 := by
  intro hz
  have h := congrArg f (product_inverse R c)
  rw [map_mul, map_one, hz, zero_mul] at h
  exact zero_ne_one h

theorem coefficient0_image {K : Type*} [Field K] (f : Order R c →+* K) :
    f (coefficient0 R c) = (2765952000 : K)^2 / f (poleProduct R c) := by
  apply (eq_div_iff (image_product_ne R c f)).2
  rw [←map_mul, coefficient0_cleared]
  simp only [map_pow, map_ofNat]

theorem coefficient1_image {K : Type*} [Field K] (f : Order R c →+* K) :
    f (coefficient1 R c) = f (coordinate R c) *
      ((2765952000 : K)^2 / f (poleProduct R c)) := by
  rw [coefficient1, map_mul, coefficient0_image]

end IntegralContactOpenSections318
