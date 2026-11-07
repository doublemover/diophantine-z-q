module
public import FourEvenContacts318
public import EvenValuationNormalization318
public section
noncomputable section
namespace FourContactBranches318
set_option maxHeartbeats 900000
open IsLocalRing FourUnitCover318
variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- All four finite even values admit one actual common uniformizer and four
actual units, derived directly from the canonical DVR valuations. -/
theorem common_decomposition (f:Fin 4→R) (m:Fin 4→ℕ)
    (hv:∀i,IsDiscreteValuationRing.addVal R (f i)=((2*m i:ℕ):ℕ∞)) :
    ∃(u:Fin 4→Rˣ)(pi:R),Irreducible pi ∧ ∀i,f i=(u i:R)*pi^(2*m i) := by
  obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
  have hh:∀i:Fin 4,∃u:Rˣ,f i=(u:R)*pi^(2*m i) := by
    intro i
    have hf:f i≠0 := by
      intro hz
      have h:=hv i
      rw [hz,IsDiscreteValuationRing.addVal_zero] at h
      exact ENat.top_ne_natCast (2*m i) h
    obtain ⟨n,u,hu⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hpi
    have hn:n=2*m i:=by
      have h:=hv i
      rw [IsDiscreteValuationRing.addVal_def (f i) u hpi n hu] at h
      exact_mod_cast h
    subst n
    exact ⟨u,hu⟩
  choose u hu using hh
  exact ⟨u,pi,hpi,hu⟩

/-- An actual finite etale rank-sixteen covering algebra is constructed from
four canonical even contact values; no roots or unit decompositions are inputs. -/
theorem actual_cover (f:Fin 4→R) (m:Fin 4→ℕ) (h2:IsUnit (2:R))
    (hv:∀i,IsDiscreteValuationRing.addVal R (f i)=((2*m i:ℕ):ℕ∞)) :
    ∃(u:Fin 4→Rˣ)(pi:R),Irreducible pi ∧ (∀i,f i=(u i:R)*pi^(2*m i)) ∧
      Module.finrank R (Cover u)=16 ∧ Module.Finite R (Cover u) ∧
      Module.Free R (Cover u) ∧ Algebra.Etale R (Cover u) ∧
      Module.FaithfullyFlat R (Cover u) ∧
      ∀i,FourEvenContacts318.contactRoot u pi m i^2=algebraMap R (Cover u) (f i) := by
  obtain ⟨u,pi,hpi,hf⟩:=common_decomposition f m hv
  have hd:=finite_free_etale u h2
  refine ⟨u,pi,hpi,hf,rank_sixteen u,hd.1,hd.2.1,hd.2.2,faithfullyFlat u,?_⟩
  intro i
  rw [hf i]
  exact FourEvenContacts318.contactRoot_square u pi m i

/-- All four-root generic-fiber tuples, not just one selected tuple, are
represented by the constructed cover. -/
theorem all_actual_generic_points (f:Fin 4→R) (m:Fin 4→ℕ)
    (hv:∀i,IsDiscreteValuationRing.addVal R (f i)=((2*m i:ℕ):ℕ∞))
    (L:Type*) [Field L] [Algebra R L] (hi:Function.Injective (algebraMap R L)) :
    ∃(u:Fin 4→Rˣ)(pi:R),Irreducible pi ∧ (∀i,f i=(u i:R)*pi^(2*m i)) ∧
      ∀y:Fin 4→L,(∀i,y i^2=algebraMap R L (f i))→
        ∃φ:Cover u→ₐ[R]L,∀i,φ (FourEvenContacts318.contactRoot u pi m i)=y i := by
  obtain ⟨u,pi,hpi,hf⟩:=common_decomposition f m hv
  refine ⟨u,pi,hpi,hf,?_⟩
  intro y hy
  apply FourEvenContacts318.all_field_points u pi m L
    (by simpa only [map_zero] using hi.ne hpi.ne_zero) y
  intro i
  rw [←hf i]
  exact hy i

variable (u:Fin 4→Rˣ) (h2:IsUnit (2:R))
include h2

/-- Every prime of the simultaneous cover has actual ramification index one. -/
theorem all_prime_indices (q:Ideal (Cover u)) [q.IsPrime] :
    Algebra.IsUnramifiedAt R q ∧ q.ramificationIdx R=1 := by
  letI:Algebra.Etale R (Cover u):=(finite_free_etale u h2).2.2
  exact ⟨inferInstance,Ideal.ramificationIdx_eq_one q R⟩

variable (q:Ideal (Cover u)) [q.IsPrime] [q.LiesOver (maximalIdeal R)]

theorem branch_domain : IsDomain (Localization.AtPrime q) := by
  letI:Algebra.Etale R (Cover u):=(finite_free_etale u h2).2.2
  exact EtalePrimeDVR318.local_domain R (Cover u) q

theorem branch_dvr : letI:=branch_domain u h2 q;
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  letI:Algebra.Etale R (Cover u):=(finite_free_etale u h2).2.2
  exact EtalePrimeDVR318.local_dvr R (Cover u) q

theorem branch_value (x:R) :
    letI:=branch_domain u h2 q
    letI:=branch_dvr u h2 q
    IsDiscreteValuationRing.addVal (Localization.AtPrime q)
      (algebraMap R (Localization.AtPrime q) x)=IsDiscreteValuationRing.addVal R x := by
  letI:Algebra.Etale R (Cover u):=(finite_free_etale u h2).2.2
  exact EtalePrimeDVR318.local_value R (Cover u) q x

end FourContactBranches318
