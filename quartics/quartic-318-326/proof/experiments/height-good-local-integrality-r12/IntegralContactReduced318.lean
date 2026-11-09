module
public import IntegralContactOpenFrame318
public import EtaleFlatReduced318
public section
noncomputable section
namespace IntegralContactReduced318
open IntegralContactOpenFrame318 Polynomial
open scoped TensorProduct nonZeroDivisors
set_option maxHeartbeats 500000
variable (R : Type*) [CommRing R] [IsDomain R] (c : Fin 4 → Rˣ)

/-- Collisions between the four contacts in positive characteristic do not
make their product the zero polynomial. -/
theorem denominator_ne_zero : denominator R ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Polynomial.X_sub_C_ne_zero _

/-- The actual punctured affine-line base remains a domain in every domain
of coefficients, including residue characteristic with collided contacts. -/
theorem base_domain : IsDomain (Base R) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (Base R)
    (M := Submonoid.powers (denominator R))
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (denominator_ne_zero R))

/-- Reducedness is proved for the original four-root order, without requiring
its components to remain connected after specialization. -/
theorem order_reduced (h2 : IsUnit (2 : R)) : IsReduced (Order R c) := by
  letI : IsDomain (Base R) := base_domain R
  letI : Module.Free (Base R) (Order R c) := (finite_free_etale R c h2).2.1
  letI : Algebra.Etale (Base R) (Order R c) := (finite_free_etale R c h2).2.2
  exact EtaleFlatReduced318.reduced (Base R) (Order R c)

variable (K : Type*) [Field K] [Algebra (Base R) K]
/-- The actual fiber is a tensor product of the given integral order, not
an independently chosen field algebra with matching equations. -/
abbrev Fiber := K ⊗[Base R] Order R c

/-- All field-valued points of the original noncontact base are covered,
including extensions of residue fields. -/
theorem fiber_reduced (h2 : IsUnit (2 : R)) : IsReduced (Fiber R c K) := by
  letI : Algebra.Etale (Base R) (Order R c) := (finite_free_etale R c h2).2.2
  exact Algebra.FormallyUnramified.isReduced_of_field K (Fiber R c K)

/-- The canonical base-change comparison retains each of the four original
coefficients, without replacing the tensor-product fiber by a quotient field. -/
@[expose] def fiberPresentation :
    Fiber R c K ≃ₐ[K] FourRootOrder318.Order (fun i =>
      algebraMap (Base R) K (algebraMap R[X] (Base R) (coefficient R c i))) :=
  FourRootOrder318.baseChange _ K

end IntegralContactReduced318
