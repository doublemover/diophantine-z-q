module
public import PurePowerIntegralPerturbation318
public import MonomialDegreeMap318
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace FinitePolynomialPowerPerturbation318
open Polynomial MonomialDegreeFiltration318 MonomialDegreeExhaustion318
variable {ι K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [CommRing A] [Nontrivial A] [Algebra K A]

/-- Starting with ANY whole finite polynomial normalization, arbitrary
specified elements can be added to sufficiently high pure powers of its
coordinates while retaining WHOLE finiteness. Coefficient degree bounds
are chosen in the old polynomial ring before the new scalar map exists.
This is an algebraic finite-normalization construction, not a properness
or generic-field finiteness assumption. -/
theorem exists_finite_perturbation (b l : ι → A)
    (hfinite : (MvPolynomial.aeval b : MvPolynomial ι K →ₐ[K] A).Finite) :
    ∃ M : ℕ, 2 ≤ M ∧
      (MvPolynomial.aeval (fun i => l i+b i^M) : MvPolynomial ι K →ₐ[K] A).Finite := by
  classical
  let R := MvPolynomial ι K
  let old : R →ₐ[K] A := MvPolynomial.aeval b
  have hpolys : ∃ P : ι → Polynomial R, ∀ i,
      (P i).Monic ∧ 0 < (P i).natDegree ∧ (P i).eval₂ old.toRingHom (-l i) = 0 := by
    letI : Algebra R A := old.toAlgebra
    letI : Module.Finite R A := hfinite
    refine ⟨fun i => minpoly R (-l i),fun i => ?_⟩
    have hi : IsIntegral R (-l i) := IsIntegral.of_finite R _
    exact ⟨minpoly.monic hi,minpoly.natDegree_pos hi,minpoly.aeval R (-l i)⟩
  obtain ⟨P,hP⟩ := hpolys
  let e : ι → ℕ := fun i => (P i).natDegree-1
  have he (i : ι) : (P i).natDegree = e i+1 := by
    have hi : 0 < (P i).natDegree := (hP i).2.1
    dsimp [e]
    omega
  let J := Σ i, Fin (e i+1)
  let coeff : J → R := fun j => (P j.1).coeff j.2.val
  have hcgen (j : J) : coeff j ∈ Algebra.adjoin K (Set.range (MvPolynomial.X : ι → R)) := by
    rw [MvPolynomial.adjoin_range_X]
    exact Algebra.mem_top
  obtain ⟨D,hDcoeff⟩ := exists_uniform_degree (MvPolynomial.X : ι → R) coeff hcgen
  let M := max (D+1) 2
  have hDM : D < M := lt_of_lt_of_le (Nat.lt_succ_self D) (le_max_left _ _)
  let g : R →ₐ[K] A := MvPolynomial.aeval (fun i => l i+b i^M)
  letI : Algebra R A := g.toAlgebra
  letI : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  have hgX (i : ι) : algebraMap R A (MvPolynomial.X i) = l i+b i^M := MvPolynomial.aeval_X _ _
  have hcoeff (i : ι) (k : ℕ) (hk : k < e i+1) :
      old ((P i).coeff k) ∈ piece (R:=R) b D := by
    have h := MonomialDegreeMap318.map_mem old (MvPolynomial.X : ι → R)
      (hDcoeff ⟨i,⟨k,hk⟩⟩)
    have h' : old ((P i).coeff k) ∈ piece (R:=K) b D := by
      simpa only [coeff,old,MvPolynomial.aeval_X] using h
    exact extend_scalars b h'
  have hrel (i : ι) :
      (b i^M-algebraMap R A (MvPolynomial.X i))^(e i+1) +
        ∑ k ∈ Finset.range (e i+1), old ((P i).coeff k)*
          (b i^M-algebraMap R A (MvPolynomial.X i))^k = 0 := by
    have ha : b i^M-algebraMap R A (MvPolynomial.X i) = -l i := by rw [hgX]; ring
    rw [ha]
    have hp := (hP i).2.2
    rw [Polynomial.eval₂_eq_sum_range,he i,Finset.sum_range_succ,
      ←he i,(hP i).1.coeff_natDegree,map_one,one_mul] at hp
    simpa only [he i,add_comm] using hp
  let S : Subalgebra R A := Algebra.adjoin R (Set.range b)
  letI : Module.Finite R S :=
    PurePowerReductionFiniteAlgebra318.finite_adjoin b (fun i => M*(e i+1))
      (fun i => PurePowerIntegralPerturbation318.reduction b i M D (e i)
        (MvPolynomial.X i) (fun k => old ((P i).coeff k)) hDM (hcoeff i) (hrel i))
  let bS : ι → S := fun i => ⟨b i,Algebra.subset_adjoin ⟨i,rfl⟩⟩
  let oldS : R →ₐ[K] S := MvPolynomial.aeval bS
  let incl : S →ₐ[K] A := S.val.restrictScalars K
  have hsquare : incl.comp oldS = old := by
    ext i
    simp only [AlgHom.comp_apply,oldS,MvPolynomial.aeval_X,old,incl,
      AlgHom.restrictScalars_apply,Subalgebra.val_apply,bS]
  have hIncl : incl.Finite := AlgHom.Finite.of_comp_finite
    (f:=oldS) (g:=incl) (hsquare.symm ▸ hfinite)
  letI : Module.Finite S A := hIncl
  refine ⟨M,le_max_right _ _,?_⟩
  change Module.Finite R A
  exact Module.Finite.trans S A
end FinitePolynomialPowerPerturbation318
