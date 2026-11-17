module
public import ActualOddRegularLift318
public section
noncomputable section
namespace ActualOddBadPrimeObstruction318
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualOddRegularLift318
open ActualPrimitivePrimePower318 ActualAmbientQuadricLift318
set_option maxHeartbeats 26000000

/-- If kappa has valuation exactly one, a residue with all first four
coordinates divisible by p cannot have a unit w and solve Q modulo p^2.
This is an actual integer divisibility obstruction, not a smoothness claim. -/
theorem actual_valuation_one_obstruction (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (x : Coordinates ℤ)
    (hQ : (p:ℤ)^2∣equation κ x)
    (ha : (p:ℤ)∣x.1.1) (hb : (p:ℤ)∣x.1.2)
    (hc : (p:ℤ)∣x.2.1.1) (hd : (p:ℤ)∣x.2.1.2) : (p:ℤ)∣x.2.2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  obtain ⟨u,hu⟩ := hκ
  have hun : ¬(p:ℤ)∣u := by
    rintro ⟨v,hv⟩
    apply hκ2
    refine ⟨v,?_⟩
    rw [hu,hv]
    ring
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  obtain ⟨c,hc⟩ := hc
  obtain ⟨d,hd⟩ := hd
  obtain ⟨q,hq⟩ := hQ
  have he : (p:ℤ)^2∣(p:ℤ)*(u*x.2.2^2) := by
    refine ⟨a^2+b^2-(c^2+d^2)-q,?_⟩
    dsimp [equation] at hq
    rw [ha,hb,hc,hd,hu] at hq
    nlinarith [hq]
  rw [pow_two,mul_dvd_mul_iff_left hp0] at he
  have hue : (u:ZMod p)≠0 := by
    intro hz
    exact hun ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp hz)
  have hz : (u:ZMod p)*(x.2.2:ZMod p)^2=0 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (u*x.2.2^2) p).mpr he
    simpa only [Int.cast_mul,Int.cast_pow] using hh
  have hw : (x.2.2:ZMod p)=0 := (sq_eq_zero_iff).mp ((mul_eq_zero.mp hz).resolve_left hue)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd x.2.2 p).mp hw

/-- At every modulus divisible by p^2, ALL original primitive points
are regular when the original kappa has valuation one at p. -/
theorem actual_primitive_is_regular (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (hpm : p^2∣m)
    (x : Quadric (κ:ZMod m)) (hx : IsPrimitive κ m p x) :
    Regular (mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hh
  have hfirst : ((mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1)).1,
      (mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1)).2.1)=((0,0),(0,0)) :=
    not_not.mp hh
  have hA := congrArg (fun z : (ZMod p×ZMod p)×(ZMod p×ZMod p) => z.1.1) hfirst
  have hB := congrArg (fun z : (ZMod p×ZMod p)×(ZMod p×ZMod p) => z.1.2) hfirst
  have hC := congrArg (fun z : (ZMod p×ZMod p)×(ZMod p×ZMod p) => z.2.1) hfirst
  have hD := congrArg (fun z : (ZMod p×ZMod p)×(ZMod p×ZMod p) => z.2.2) hfirst
  have hdiv : (p:ℤ)^2∣equation κ (digits m x.1) :=
    (by exact_mod_cast hpm : (p:ℤ)^2∣(m:ℤ)).trans (actual_base_divides κ m x)
  have hw := actual_valuation_one_obstruction κ p hp hκ hκ2 (digits m x.1) hdiv
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hA)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hB)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hC)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hD)
  have hW := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hw
  apply hx
  exact Prod.ext (Prod.ext hA hB) (Prod.ext (Prod.ext hC hD) hW)

end ActualOddBadPrimeObstruction318
