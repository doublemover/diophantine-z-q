module
public import FractionKaehlerFrame318
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public section
noncomputable section

namespace SelectedLocalDVRCanonical318

open FractionKaehlerFrame318 KaehlerFrame318

variable {R B K : Type*} [Field R] [CharZero R]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [IsFractionRing B K]

local notation "ι" => algebraMap B K
local notation "v" => ValuationRing.valuation B K

/-- The actual field Kähler coefficient of the literal differential dJ in
the frame constructed by mapping the integral frame. -/
@[expose] def coefficient (frame : KaehlerDifferential R B ≃ₗ[B] B) (J : K) : K :=
  genericFrame frame (KaehlerDifferential.D R K J)

theorem coefficient_eq (frame : KaehlerDifferential R B ≃ₗ[B] B) (J : K) :
    coefficient frame J = derived frame J := by
  change genericFrame frame (KaehlerDifferential.D R K J) = _
  rw [← frameDerivation_apply, genericFrame_derivation]

/-- Exact nonvanishing of the residual leading term, for positive as
well as negative exponents. The integer is a unit via the coefficient
field R, not just nonzero in the fraction field K. -/
theorem leading_isUnit (δ : Derivation R B B) (z : B) (hz : Irreducible z)
    (n : ℤ) (hn : n ≠ 0) (u : Bˣ) :
    IsUnit ((n:B)*(u:B) + z*δ u) := by
  have hnR : (n:R) ≠ 0 := by exact_mod_cast hn
  have hnB : IsUnit (n:B) := by
    simpa only [map_intCast] using ((isUnit_iff_ne_zero.mpr hnR).map (algebraMap R B))
  have hUnit : IsUnit ((n:B)*(u:B)) := hnB.mul u.isUnit
  have hZ : IsLocalRing.residue B z = 0 := by
    by_contra h
    exact hz.not_isUnit ((IsLocalRing.residue_ne_zero_iff_isUnit z).mp h)
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  simpa only [map_add, map_mul, hZ, zero_mul, add_zero] using
    (hUnit.map (IsLocalRing.residue B)).ne_zero

/-- Genuine signed-power Leibniz rule in the actual fraction Kähler
frame. No formal-power-series comparison or completion is needed. -/
theorem coefficient_unit_power (frame : KaehlerDifferential R B ≃ₗ[B] B)
    (z : B) (hz : Irreducible z) (dz : frame (KaehlerDifferential.D R B z) = 1)
    (n : ℤ) (hn : n ≠ 0) (u : Bˣ) :
    ∃ w : Bˣ, coefficient frame ((ι z)^n * ι (u:B)) =
      (ι z)^(n-1) * ι (w:B) := by
  let D := derived (K := K) frame
  let δ := frameDerivation frame
  have hD (b : B) : D (ι b) = ι (δ b) :=
    FractionDerivation318.extend_integral δ b
  have hDz : D (ι z) = 1 := by
    rw [hD, show δ z = 1 from dz, map_one]
  have hzn : ι z ≠ 0 :=
    fun h => hz.ne_zero ((IsFractionRing.injective B K) (h.trans (map_zero ι).symm))
  have hs : (ι z)^(n-1) * ι z = (ι z)^n := by
    calc
      _ = (ι z)^(n-1) * (ι z)^(1:ℤ) := by rw [zpow_one]
      _ = (ι z)^((n-1)+1) := (zpow_add₀ hzn _ _).symm
      _ = _ := by rw [sub_add_cancel]
  have hU := leading_isUnit δ z hz n hn u
  refine ⟨hU.unit, ?_⟩
  rw [coefficient_eq, hU.unit_spec]
  change D ((ι z)^n * ι (u:B)) = (ι z)^(n-1) * ι ((n:B)*(u:B)+z*δ u)
  rw [D.leibniz, D.leibniz_zpow, hDz, hD]
  simp only [smul_eq_mul, mul_one, zsmul_eq_mul, map_add, map_mul, map_intCast]
  rw [← hs]
  ring

/-- Read a unit-power factorization from the actual canonical valuation
of the same fraction field. This also works for negative powers. -/
theorem unit_power_of_value (z : B) (hz : Irreducible z) (J : K) (n : ℤ)
    (hJ : v J = (v (ι z))^n) :
    ∃ u : Bˣ, J = (ι z)^n * ι (u:B) := by
  have hzK : ι z ≠ 0 :=
    fun h => hz.ne_zero ((IsFractionRing.injective B K) (h.trans (map_zero ι).symm))
  have hzpow : (ι z)^n ≠ 0 := zpow_ne_zero _ hzK
  have hvpow : v ((ι z)^n) ≠ 0 := Valuation.ne_zero_of_unit v (Units.mk0 _ hzpow)
  have hQ : v (J/(ι z)^n) = 1 := by
    rw [Valuation.map_div v, hJ, ← map_zpow₀ v (ι z) n, div_self hvpow]
  obtain ⟨b,hb⟩ := (ValuationRing.integers B K).exists_of_le_one hQ.le
  have hbunit : IsUnit b :=
    (ValuationRing.integers B K).isUnit_of_one' (show v (ι b) = 1 from (congrArg v hb).trans hQ)
  refine ⟨hbunit.unit, ?_⟩
  rw [hbunit.unit_spec, hb, mul_comm, div_mul_cancel₀ _ hzpow]

/-- An order n ≠ 0 for an actual field function forces exactly n−1 for
its literal differential, in the normalized integral dz frame. -/
theorem signed_order (frame : KaehlerDifferential R B ≃ₗ[B] B)
    (z : B) (hz : Irreducible z) (dz : frame (KaehlerDifferential.D R B z) = 1)
    (J : K) (n : ℤ) (hn : n ≠ 0) (hJ : v J = (v (ι z))^n) :
    v (coefficient frame J) = (v (ι z))^(n-1) := by
  obtain ⟨u,hu⟩ := unit_power_of_value z hz J n hJ
  obtain ⟨w,hw⟩ := coefficient_unit_power (K := K) frame z hz dz n hn u
  rw [hu, hw, map_mul, map_zpow₀ v, (ValuationRing.integers B K).one_of_isUnit w.isUnit,
    mul_one]

/-- At any finite branch use J−a only for its order. The coefficient
that is measured is that of the original dJ, using the same frame. -/
theorem finite_order (frame : KaehlerDifferential R B ≃ₗ[B] B)
    (z : B) (hz : Irreducible z) (dz : frame (KaehlerDifferential.D R B z) = 1)
    (J : K) (a : R) (e : ℕ) (he : 0 < e)
    (hJ : v (J-algebraMap R K a) = (v (ι z))^(e:ℤ)) :
    v (coefficient frame J) = (v (ι z))^((e:ℤ)-1) := by
  have hcoeff : coefficient frame (J-algebraMap R K a) = coefficient frame J := by
    simp only [coefficient_eq, map_sub, Derivation.map_algebraMap, sub_zero]
  have hn : (e:ℤ) ≠ 0 := by omega
  simpa only [hcoeff] using signed_order frame z hz dz (J-algebraMap R K a) (e:ℤ) hn hJ

/-- A pole of width w yields −w−1 for dJ itself, not for d(1/J). -/
theorem cusp_order (frame : KaehlerDifferential R B ≃ₗ[B] B)
    (z : B) (hz : Irreducible z) (dz : frame (KaehlerDifferential.D R B z) = 1)
    (J : K) (w : ℕ) (hw : 0 < w) (hJ : v J = (v (ι z))^(-(w:ℤ))) :
    v (coefficient frame J) = (v (ι z))^(-(w:ℤ)-1) := by
  have hn : -(w:ℤ) ≠ 0 := by omega
  exact signed_order frame z hz dz J (-(w:ℤ)) hn hJ

end SelectedLocalDVRCanonical318

#print axioms SelectedLocalDVRCanonical318.coefficient_eq
#print axioms SelectedLocalDVRCanonical318.signed_order
#print axioms SelectedLocalDVRCanonical318.finite_order
#print axioms SelectedLocalDVRCanonical318.cusp_order
