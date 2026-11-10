module
public import PELQuaternionScalarExtension318
public section
noncomputable section
namespace PELOriginalLocalAlgebraClassification318
open PELQuaternionAlgebra318 PELPrimeNormalizerData318
open scoped TensorProduct
set_option maxHeartbeats 1400000

/-- Actual scalar extension of the original rational B at a finite prime. -/
abbrev CompletedAlgebra (p : ℕ) [Fact p.Prime] := ℚ_[p] ⊗[ℚ] B

@[expose] def presentation (p : ℕ) [Fact p.Prime] :
    CompletedAlgebra p ≃ₐ[ℚ_[p]] QuaternionAlgebra ℚ_[p] (-210) 0 5 :=
  PELQuaternionScalarExtension318.equivalence ℚ_[p]

/-- Local division is now a theorem about the genuine tensor extension of
the ORIGINAL rational B, not merely an isomorphic-looking presentation. -/
theorem ramified_division (i : Fin 4) (z : CompletedAlgebra (prime i)) (hz : z≠0) : IsUnit z := by
  let e := presentation (prime i)
  have he : e z≠0 := by
    intro h
    apply hz
    exact e.injective (h.trans (map_zero e).symm)
  obtain ⟨v,hv⟩ := PELActualRamifiedQuaternion318.every_nonzero_isUnit i (e z) he
  refine ⟨Units.map e.symm.toMonoidHom v,?_⟩
  change e.symm (v : QuaternionAlgebra ℚ_[prime i] (-210) 0 5)=z
  rw [hv,e.symm_apply_apply]

/-- Literal matrix splitting of the original rational B after base change
to each actual Q_p outside210. -/
@[expose] def unramified_splitting (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) :
    CompletedAlgebra p ≃+* Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  (presentation p).toRingEquiv.trans (PELActualUnramifiedSplitting318.splitting p hp210)

theorem unramified_original (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) (q : B) :
    unramified_splitting p hp210 (1 ⊗ₜ[ℚ] q)=
      PELActualUnramifiedSplitting318.originalRepresentation p hp210 q := by
  change PELActualUnramifiedSplitting318.splitting p hp210
    (PELQuaternionScalarExtension318.equivalence ℚ_[p] (1 ⊗ₜ[ℚ] q))=_
  rw [PELQuaternionScalarExtension318.equivalence_original] <;> rfl

theorem unramified_original_norm (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) (q : B) :
    (unramified_splitting p hp210 (1 ⊗ₜ[ℚ] q)).det=(reducedNorm q:ℚ_[p]) := by
  rw [unramified_original]
  exact PELActualUnramifiedSplitting318.original_norm p hp210 q

theorem unramified_scalar (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) (a : ℚ_[p]) :
    unramified_splitting p hp210 (algebraMap ℚ_[p] (CompletedAlgebra p) a)=
      algebraMap ℚ_[p] (Matrix (Fin 2) (Fin 2) ℚ_[p]) a := by
  change PELActualUnramifiedSplitting318.splitting p hp210
    (presentation p (algebraMap ℚ_[p] (CompletedAlgebra p) a))=_
  rw [(presentation p).commutes]
  exact PELActualUnramifiedSplitting318.splitting_scalar p hp210 a

theorem unramified_zero_divisors (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) :
    ∃ a b : CompletedAlgebra p, a≠0 ∧ b≠0 ∧ a*b=0 := by
  obtain ⟨a,b,ha,hb,hab⟩ := PELActualUnramifiedSplitting318.zero_divisors p hp210
  let e := presentation p
  refine ⟨e.symm a,e.symm b,?_,?_,?_⟩
  · exact fun h => ha (e.symm.injective (h.trans (map_zero e.symm).symm))
  · exact fun h => hb (e.symm.injective (h.trans (map_zero e.symm).symm))
  · rw [←map_mul,hab,map_zero]

theorem ramified_coverage (p : ℕ) [hp : Fact p.Prime] (h : p ∣ 210) :
    ∃ i : Fin 4, prime i=p := by
  apply (prime_coverage p).mpr
  change p ∣ (2*3*5*7) at h
  rw [hp.1.dvd_mul,hp.1.dvd_mul,hp.1.dvd_mul] at h
  rcases h with ((h2|h3)|h5)|h7
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp h2)
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp h3))
  · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp h5)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp h7)))

/-- Exact finite-prime classification on the genuine scalar extension:
every nonzero element is a unit if and only if p divides the original210. -/
theorem division_iff (p : ℕ) [Fact p.Prime] :
    (∀ z : CompletedAlgebra p, z≠0 → IsUnit z) ↔ p ∣ 210 := by
  constructor
  · intro h
    by_contra hp210
    obtain ⟨a,b,ha,hb,hab⟩ := unramified_zero_divisors p hp210
    have hb0 : b=0 := (h a ha).mul_left_cancel (hab.trans (mul_zero a).symm)
    exact hb hb0
  · intro hp210 z hz
    obtain ⟨i,hi⟩ := ramified_coverage p hp210
    subst p
    exact ramified_division i z hz
end PELOriginalLocalAlgebraClassification318
