module
public import ActualTwoDescentEllipticModel318
public section
noncomputable section

namespace ActualSelectedPointedFrickeCusp318
open ActualTwoDescentEllipticModel318

/-- At the actual rational elliptic target, the based Abel formula and the
+1 action on the same modular quotient yield the pointed Fricke constant. -/
theorem pointed_fricke_translation (n : ℚ) {X J : Type*} [AddCommGroup J]
    (w : X → X) (base : X) (AJ : X → J) (W : J →+ J) (φ : J →+ Point n)
    (hAJ : ∀ x : X, AJ (w x) = W (AJ x) + AJ (w base))
    (hW : ∀ z : J, φ (W z) = φ z) (x : X) :
    φ (AJ (w x)) = φ (AJ x) + φ (AJ (w base)) := by
  rw [hAJ x, map_add, hW]

/-- For full Fricke with eigenvalue +1, the exact constant on the pointed
map is two-torsion by involutivity. No assertion for other cusps or for
Fricke sign -1 is made. -/
theorem fricke_cusp_two_nsmul_zero (n : ℚ) {X : Type*}
    (w : X → X) (base : X) (π : X → Point n) (hw : Function.Involutive w)
    (hbase : π base = 0)
    (hplus : ∀ x : X, π (w x) = π x + π (w base)) :
    (2 : ℕ) • π (w base) = 0 := by
  have h := hplus (w base)
  rw [hw base, hbase] at h
  simpa only [two_nsmul] using h.symm

/-- Transport the two-torsion relation to the original already-even
multiplier, without choosing a new multiple or altering the Heegner sum. -/
theorem fricke_cusp_even_nsmul_zero (n : ℚ) {X : Type*}
    (w : X → X) (base : X) (π : X → Point n) (hw : Function.Involutive w)
    (hbase : π base = 0)
    (hplus : ∀ x : X, π (w x) = π x + π (w base))
    (m : ℕ) (hm : 2 ∣ m) :
    m • π (w base) = 0 := by
  obtain ⟨k, hk⟩ := hm
  have h₂ := fricke_cusp_two_nsmul_zero n w base π hw hbase hplus
  rw [hk, Nat.mul_comm 2 k, mul_nsmul, h₂, nsmul_zero]

end ActualSelectedPointedFrickeCusp318
