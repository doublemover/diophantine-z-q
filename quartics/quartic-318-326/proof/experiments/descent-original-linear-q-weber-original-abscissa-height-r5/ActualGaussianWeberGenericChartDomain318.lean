module
public import ActualGaussianWeberQuadraticGenericChart318
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.GaussLemma
public section
noncomputable section

namespace ActualGaussianWeberGenericChartDomain318

open Polynomial ActualGaussianWeberQuadraticGenericChart318

variable (K : Type*) [Field K]

private theorem cubic_degree : ((X:K[X])^3-X).natDegree=3 := by
  have h : (X:K[X]).natDegree < ((X:K[X])^3).natDegree := by
    rw [natDegree_pow,natDegree_X]
    decide
  rw [natDegree_sub_eq_left_of_natDegree_lt h,natDegree_pow,natDegree_X] <;> decide

/-- The exact curve polynomial x³−x is not a square even in the
rational function field, by parity of the two cleared degrees. This
does not rely on a residue root count or a characteristic assumption. -/
theorem cubic_not_square (r : RatFunc K) :
    r^2≠algebraMap K[X] (RatFunc K) ((X:K[X])^3-X) := by
  intro H
  let c : K[X] := (X:K[X])^3-X
  have hc : c.natDegree=3 := cubic_degree K
  have hcz : c≠0 := by
    intro h
    rw [h,natDegree_zero] at hc
    omega
  have hmap : Function.Injective (algebraMap K[X] (RatFunc K)) :=
    RatFunc.algebraMap_injective K
  have hden : algebraMap K[X] (RatFunc K) (r.denom^2)≠0 := by
    intro h
    exact pow_ne_zero 2 (RatFunc.denom_ne_zero r) (hmap (h.trans (map_zero _).symm))
  have h : algebraMap K[X] (RatFunc K) (r.num^2) /
      algebraMap K[X] (RatFunc K) (r.denom^2) =
      algebraMap K[X] (RatFunc K) c := by
    rw [map_pow,map_pow,←div_pow,RatFunc.num_div_denom]
    exact H
  have he : r.num^2=c*r.denom^2 :=
    hmap (by simpa only [map_mul] using (div_eq_iff hden).mp h)
  have hd := congrArg natDegree he
  simp only [natDegree_pow,natDegree_mul hcz (pow_ne_zero _ (RatFunc.denom_ne_zero r)),hc] at hd
  omega

theorem relation_irreducible : Irreducible (relation K) := by
  have hm : (relation K).Monic := monic_X_pow_sub_C _ (by decide)
  apply (hm.irreducible_iff_irreducible_map_fraction_map (K:=RatFunc K)).2
  have hre : (relation K).map (algebraMap K[X] (RatFunc K)) =
      X^2-C (algebraMap K[X] (RatFunc K) ((X:K[X])^3-X)) := by
    simp only [relation,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  rw [hre]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_sub_C]
    decide
  · intro r hr
    apply cubic_not_square K r
    simpa only [Polynomial.IsRoot,eval_sub,eval_pow,eval_X,eval_C,sub_eq_zero] using hr

/-- The literal original affine chart is integral over every field.
This is the actual residue-domain input to a curve Gauss place. -/
theorem chart_isDomain : IsDomain (Chart K) :=
  AdjoinRoot.isDomain_of_prime (relation_irreducible K).prime

/-- Base change of the fixed affine chart is faithful on elements
whenever the coefficient ring map is injective. -/
theorem mapChart_injective {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial R] [Nontrivial S] (f : R→+*S) (hf : Function.Injective f) :
    Function.Injective (mapChart f) := by
  intro u v h
  obtain ⟨a,b,hu⟩ := element_surjective u
  obtain ⟨c,d,hv⟩ := element_surjective v
  rw [←hu,←hv,element_map,element_map] at h
  obtain ⟨hac,hbd⟩ := element_coefficients h
  rw [←hu,←hv,Polynomial.map_injective f hf hac,Polynomial.map_injective f hf hbd]

/-- The actual map on chart elements is surjective when the
coefficient residue map is surjective. Lifts are taken separately
in the free coordinates 1,Y and then recombined in the quotient. -/
theorem mapChart_surjective {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial S] (f : R→+*S) (hf : Function.Surjective f) :
    Function.Surjective (mapChart f) := by
  intro z
  obtain ⟨a,b,hz⟩ := element_surjective z
  obtain ⟨a₀,ha⟩ := Polynomial.map_surjective f hf a
  obtain ⟨b₀,hb⟩ := Polynomial.map_surjective f hf b
  refine ⟨element a₀ b₀,?_⟩
  rw [element_map,ha,hb,hz]

end ActualGaussianWeberGenericChartDomain318
