module
public import Height13RealLog
public section
namespace EvenPhase

/-- A square identity for every vector gives a single proportionality
constant for the two coefficient functionals. No multiplicity-one or
one-dimensional eigenspace assumption is needed. -/
theorem coefficient_functionals_proportional {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (f g : V →ₗ[K] K)
    (C : K) (v0 : V) (h0 : f v0=1)
    (hsquare : ∀ v, (g v)^2=C*(f v)^2) :
    ∀ v, g v=g v0*f v := by
  intro v
  have hf : f (v-f v • v0)=0 := by simp [h0]
  have hz : g (v-f v • v0)=0 := by
    have hh := hsquare (v-f v • v0)
    rw [hf] at hh
    simpa using hh
  have he : g v-f v*g v0=0 := by simpa using hz
  simpa [mul_comm] using sub_eq_zero.mp he

/-- Galois conjugation and the explicitly chosen local-root phase have
identical multiplier, so their quotient is fixed. The multiplier is not
assumed to be a sign. -/
theorem galois_phase_quotient {K : Type*} [Field K]
    (tau : K ≃+* K) (a z nu : K) (hz : z≠0)
    (ha : tau a=nu*a) (hp : tau z=nu*z) : tau (a/z)=a/z := by
  have hnu : nu≠0 := by
    intro hn
    have htz : tau z=0 := by rw [hp,hn,zero_mul]
    exact hz (tau.injective (by simpa using htz))
  rw [map_div₀,ha,hp,mul_div_mul_left _ _ hnu]

/-- Removing the explicit phase from the literal square identity leaves
exactly the ratio of normalized central values. -/
theorem phase_stripped_square {K : Type*} [Field K]
    (z r L : K) (hz : z≠0) (h : (z*r)^2=z^2*L) : r^2=L := by
  rw [mul_pow] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hz) h

/-- Once rationality and the even lower bound supply integral depths, the
minimum is attained on the original fixed retained set. -/
theorem fixed_attained_minimum {D : Type*} (retained : D → Prop)
    (depth : D → ℤ) (C : ℤ) (hne : ∃ d, retained d)
    (hbound : ∀ d, retained d → C≤depth d) :
    ∃ delta, (∃ d, retained d ∧ depth d=delta) ∧
      ∀ d, retained d → delta≤depth d := by
  have hnonempty : ∃ z, ∃ d, retained d ∧ depth d=z := by
    obtain ⟨d,hd⟩ := hne
    exact ⟨depth d,d,hd,rfl⟩
  obtain ⟨delta,hd,hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ d, retained d ∧ depth d=z)
    ⟨C,by rintro z ⟨d,hr,rfl⟩; exact hbound d hr⟩ hnonempty
  exact ⟨delta,hd,fun d hr => hmin (depth d) ⟨d,hr,rfl⟩⟩

/-- Later exclusions inherit the original lower bound; they do not change
its normalization or reselect a minimum. -/
theorem later_sieve_same_bound {D : Type*} (retained extra : D → Prop)
    (depth : D → ℤ) (delta : ℤ)
    (hmin : ∀ d, retained d → delta≤depth d) :
    ∀ d, retained d ∧ extra d → delta≤depth d := by
  intro d hd
  exact hmin d hd.1

end EvenPhase
#print axioms EvenPhase.coefficient_functionals_proportional
#print axioms EvenPhase.galois_phase_quotient
#print axioms EvenPhase.phase_stripped_square
#print axioms EvenPhase.fixed_attained_minimum
#print axioms EvenPhase.later_sieve_same_bound
