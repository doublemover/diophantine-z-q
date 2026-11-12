module
public import ActualInertOrderCoverageSupport318
public section
noncomputable section
namespace SelectedGaussianCRTDivisorExclusion318
open GaussianNeighborNorms318 GaussianFiniteCoordinateCRT318 GaussianCoordinateClassScaling318
open GaussianFixedClassPrimeNormSource318
lemma translated_residues {S : Finset ℕ} (d : Class S) (z : ℤ×ℤ)
    (q : ℕ) (hq : q∈S) :
    ((translated d z).1:ZMod q)=0 ∧ ((translated d z).2:ZMod q)=1 := by
  have ha : (d.a:ZMod q)=0 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (d.aq q hq)
  have hb : (d.b:ZMod q)=1 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (d.bq q hq)
  have hP : (period S:ZMod q)=0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr
      ((Finset.dvd_prod_of_mem (fun t:ℕ => t) hq).trans (dvd_mul_left _ 112))
  simp [translated,ha,hb,hP]
lemma neighbors_nonzero (q : ℕ) (hp : q.Prime) (h2 : q≠2) (a b : ℤ)
    (ha : (a:ZMod q)=0) (hb : (b:ZMod q)=1) : ¬q∣minus a b ∧ ¬q∣plus a b := by
  have ht : (2:ZMod q)≠0 := by
    intro he
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using he)))
  constructor
  · intro hd
    have hz := (ZMod.natCast_eq_zero_iff _ q).mpr hd
    apply ht
    simpa [minus,GaussianFiniteNormResidues318.cast_norm,ha,hb] using hz
  · intro hd
    have hz := (ZMod.natCast_eq_zero_iff _ q).mpr hd
    apply ht
    simpa [plus,GaussianFiniteNormResidues318.cast_norm,ha,hb] using hz
/-- Every free prime in the fixed CRT class is excluded from EACH actual
order. Increasing that screen cannot simultaneously supply coverage by
one of its primes. This applies to inert AND split auxiliary primes. -/
theorem translated_excludes (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    {S : Finset ℕ} (d : Class S) (z : ℤ×ℤ)
    (hn : (p:ℤ)=(translated d z).1^2+(translated d z).2^2) (h7 : ¬p∣49)
    (q : ℕ) (hq : q∈S) (hp : q.Prime) (h2 : q≠2) :
    ¬q∣SelectedQuotientOrders318.order p rho hr := by
  have hfull:=full_ray d z
  have hrs : GaussianRayQuadratic318.Ray p (translated d z).1 (translated d z).2 :=
    ⟨hn,hfull.1,hfull.2.1⟩
  have hres:=translated_residues d z q hq
  have hne:=neighbors_nonzero q hp h2 _ _ hres.1 hres.2
  exact SelectedGaussianOrderPrimeSupport318.excluded p rho hr _ _ hrs
    hfull.2.2.1 hfull.2.2.2 h7 q hne.1 hne.2
/-- The exceptional historical mod7 ray also excludes7 from every
actual order, independently of the free CRT prime set. -/
lemma seven_excludes (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (a b : ℤ) (hray : GaussianRayQuadratic318.Ray p a b)
    (ha7 : a%7=1) (hb7 : b%7=3) (h7 : ¬p∣49) :
    ¬7∣SelectedQuotientOrders318.order p rho hr := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  have hz := (SelectedGaussianOrderPrimeSupport318.inert p rho hr a b hray ha7 hb7
    h7 7 (by decide) hd).2
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).mp hz
  omega
end SelectedGaussianCRTDivisorExclusion318
