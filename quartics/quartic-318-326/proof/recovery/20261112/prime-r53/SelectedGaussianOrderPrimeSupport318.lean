module
public import GaussianInertNeighborUnitNorm318
public section
noncomputable section
namespace SelectedGaussianOrderPrimeSupport318
open GaussianNeighborNorms318 SelectedReductionOrder318
variable (p : ℕ) [Fact p.Prime]
/-- Native quotient order divides its actual count. Existing Jacobi CM
identifies that SAME count with one neighboring norm; no group-law
identification with a computational residue model is required. -/
lemma neighbor (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℤ)
    (hray : GaussianRayQuadratic318.Ray p a b) (ha7 : a%7=1) (hb7 : b%7=3)
    (h7 : ¬p∣49) (q : ℕ) (hd : q∣SelectedQuotientOrders318.order p rho hr) :
    q∣minus a b ∨ q∣plus a b := by
  have hm:=GaussianRayQuadratic318.prime_mod p a b hray
  have hc:=hd.trans (actual_order_dvd p rho hr (by omega : p≠2) h7)
  rcases CanonicalSelectedCounts318.actual_count p rho hr a b hray ha7 hb7
    (CanonicalJacobiNorm318.canonical_from_ray p a b hray) with he|he
  · exact Or.inl (by rwa [he] at hc)
  · exact Or.inr (by rwa [he] at hc)
lemma excluded (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℤ)
    (hray : GaussianRayQuadratic318.Ray p a b) (ha7 : a%7=1) (hb7 : b%7=3)
    (h7 : ¬p∣49) (q : ℕ) (hm : ¬q∣minus a b) (hp : ¬q∣plus a b) :
    ¬q∣SelectedQuotientOrders318.order p rho hr := by
  intro hd
  exact (neighbor p rho hr a b hray ha7 hb7 h7 q hd).elim hm hp
lemma inert (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℤ)
    (hray : GaussianRayQuadratic318.Ray p a b) (ha7 : a%7=1) (hb7 : b%7=3)
    (h7 : ¬p∣49) (q : ℕ) [Fact q.Prime] (h3 : q%4=3)
    (hd : q∣SelectedQuotientOrders318.order p rho hr) :
    (p:ZMod q)=1 ∧ (b:ZMod q)=0 := by
  have hn:=neighbor p rho hr a b hray ha7 hb7 h7 q hd
  exact ⟨GaussianInertNeighborUnitNorm318.prime_residue q h3 p a b hray.1 hn,
    (GaussianInertNeighborUnitNorm318.residues q h3 a b hn).1⟩
end SelectedGaussianOrderPrimeSupport318
