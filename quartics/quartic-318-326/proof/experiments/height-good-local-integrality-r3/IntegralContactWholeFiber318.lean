module
public import IntegralContactOpenFrame318
public import EtaleQuotientReduced318
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Localization.Ideal
public section
noncomputable section
namespace IntegralContactWholeFiber318
open IntegralContactOpenFrame318 Polynomial
set_option maxHeartbeats 500000
variable (R : Type*) [CommRing R]

/-- The literal denominator stays monic without a separation assumption on
the contacts, including when several contacts coincide in a residue field. -/
theorem denominator_monic : (denominator R).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)

/-- No power of the actual denominator belongs to a prime ideal extended
from the coefficient ring: its leading coefficient is still one. -/
theorem denominator_disjoint (I : Ideal R) [I.IsPrime] :
    Disjoint (Submonoid.powers (denominator R) : Set R[X])
      (I.map (C : R →+* R[X]) : Set R[X]) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨n,rfl⟩ hx
  have hcoeff := (Ideal.mem_map_C_iff.mp hx) ((denominator R ^ n).natDegree)
  have hm : (denominator R ^ n).Monic := (denominator_monic R).pow n
  have hlead : (denominator R ^ n).leadingCoeff = 1 := hm
  have h1 : (1 : R) ∈ I := by
    simpa only [Polynomial.coeff_natDegree, hlead] using hcoeff
  exact (inferInstance : I.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem I h1 isUnit_one)

/-- The actual quotient of the punctured polynomial base by every prime
coefficient ideal is a domain. No generic-fiber replacement is involved. -/
theorem base_fiber_domain (I : Ideal R) [I.IsPrime] :
    IsDomain (Base R ⧸ I.map (algebraMap R (Base R))) := by
  have hp : (I.map (C : R →+* R[X])).IsPrime :=
    inferInstance
  have hq := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (denominator R)) (Base R) (I.map (C : R →+* R[X])) hp
    (denominator_disjoint R I)
  change ((I.map (algebraMap R R[X])).map (algebraMap R[X] (Base R))).IsPrime at hq
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R R[X] (Base R)] at hq
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr hq

/-- Reducedness of the whole actual arithmetic fiber of the noncontact
order, over any prime coefficient ideal. This is stronger than reducedness
of its individual fibers over field-valued points of the punctured line. -/
theorem order_fiber_reduced (c : Fin 4 → Rˣ) (h2 : IsUnit (2 : R))
    (I : Ideal R) [I.IsPrime] :
    IsReduced (Order R c ⧸ I.map (algebraMap R (Order R c))) := by
  letI : IsDomain (Base R ⧸ I.map (algebraMap R (Base R))) := base_fiber_domain R I
  letI : Module.Free (Base R) (Order R c) := (finite_free_etale R c h2).2.1
  letI : Algebra.Etale (Base R) (Order R c) := (finite_free_etale R c h2).2.2
  have h := EtaleQuotientReduced318.reduced (Base R) (Order R c)
    (I.map (algebraMap R (Base R)))
  simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq R (Base R) (Order R c)] using h

/-- In particular, the same principal base parameter used in the vertical
argument has a reduced whole affine fiber when it generates a prime ideal. -/
theorem parameter_fiber_reduced (c : Fin 4 → Rˣ) (h2 : IsUnit (2 : R)) (r : R)
    [(Ideal.span ({r} : Set R)).IsPrime] :
    IsReduced (Order R c ⧸ Ideal.span ({algebraMap R (Order R c) r} : Set (Order R c))) := by
  have h := order_fiber_reduced R c h2 (Ideal.span ({r} : Set R))
  simpa only [Ideal.map_span, Set.image_singleton] using h

end IntegralContactWholeFiber318
