module
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic
public section
noncomputable section

namespace ActualGaussianWeberPrimitiveRational318

open Polynomial IsLocalRing

variable {K : Type*} [Field K] (V : ValuationSubring K)

private theorem contained_quotient (u d : K) (hd : d≠0)
    (h : V.valuation u≤V.valuation d) : u/d∈V := by
  obtain ⟨c,hc⟩ := (V.valuation_le_iff u d).mp h
  have he : u/d=V.subtype c := (div_eq_iff hd).2 hc.symm
  rw [he]
  exact c.property

private def normalize (A : K[X]) (d : K) (h : ∀ n, A.coeff n/d∈V) : V[X] :=
  Polynomial.ofFinsupp (Finsupp.onFinset A.support
    (fun n => (⟨A.coeff n/d,h n⟩ : V))
    (fun n hn => mem_support_iff.mpr (fun e => hn (Subtype.ext (by simp [e])))))

private theorem normalize_coeff (A : K[X]) (d : K) (h : ∀ n, A.coeff n/d∈V) (n : ℕ) :
    (normalize V A d h).coeff n=(⟨A.coeff n/d,h n⟩:V) := by
  rw [normalize,coeff_ofFinsupp,Finsupp.onFinset_apply]

private theorem normalize_scale (A : K[X]) (d : K) (hd : d≠0) (h : ∀ n, A.coeff n/d∈V) :
    C d*(normalize V A d h).map V.subtype=A := by
  ext n
  rw [coeff_C_mul,coeff_map,normalize_coeff]
  change d*(A.coeff n/d)=A.coeff n
  rw [mul_comm,div_mul_cancel₀ _ hd]

private theorem normalize_natDegree (A : K[X]) (d : K) (h : ∀ n, A.coeff n/d∈V) :
    (normalize V A d h).natDegree≤A.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [normalize_coeff]
  exact Subtype.ext (by rw [coeff_eq_zero_of_natDegree_lt hn,zero_div] <;> rfl)

private theorem normalize_primitive (A : K[X]) (d : K) (hd : d≠0)
    (h : ∀ n, A.coeff n/d∈V) (n : ℕ) (hn : A.coeff n=d) :
    (normalize V A d h).map (residue V) ≠ 0 := by
  have h1 : (normalize V A d h).coeff n=1 := by
    rw [normalize_coeff]
    apply Subtype.ext
    change A.coeff n/d=1
    rw [hn,div_self hd]
  intro he
  have hz := congrArg (fun P : (ResidueField V)[X] => P.coeff n) he
  simp only [coeff_map,h1,map_one,coeff_zero] at hz
  exact one_ne_zero hz

/-- A simultaneous scaling of the two actual polynomials, selected
from a maximal-valued nonzero coefficient of the pair. In particular,
this is one scale for both A and B, not separate normalizations. -/
structure PrimitivePair (A B : K[X]) where
  scale : K
  scale_ne : scale≠0
  num : V[X]
  den : V[X]
  num_eq : C scale*(num.map V.subtype)=A
  den_eq : C scale*(den.map V.subtype)=B
  num_degree : num.natDegree≤A.natDegree
  den_degree : den.natDegree≤B.natDegree
  some_nonzero_reduction : num.map (residue V) ≠ 0 ∨ den.map (residue V) ≠ 0

/-- Every rational pair with nonzero denominator has an integral
jointly primitive presentation. Neither a uniformizer nor
completeness/discreteness of the chosen valuation is required. -/
theorem primitive_pair (A B : K[X]) (hB : B≠0) :
    Nonempty (PrimitivePair V A B) := by
  classical
  let S := A.support.image A.coeff ∪ B.support.image B.coeff
  have hS : S.Nonempty := by
    obtain ⟨n,hn⟩ := support_nonempty.mpr hB
    exact ⟨B.coeff n,Finset.mem_union_right _ (Finset.mem_image_of_mem B.coeff hn)⟩
  obtain ⟨d,hd,hmax⟩ := Finset.exists_max_image S V.valuation hS
  have hit : (∃ n ∈ A.support, A.coeff n=d) ∨ (∃ n ∈ B.support, B.coeff n=d) :=
    (Finset.mem_union.mp hd).imp Finset.mem_image.mp Finset.mem_image.mp
  have hD : d≠0 := by
    rcases hit with ⟨n,hn,rfl⟩ | ⟨n,hn,rfl⟩
    · exact mem_support_iff.mp hn
    · exact mem_support_iff.mp hn
  have hAll (P : K[X]) (hPS : P.support.image P.coeff ⊆ S) (n : ℕ) :
      P.coeff n/d∈V := by
    by_cases hzero : P.coeff n=0
    · rw [hzero,zero_div]
      exact V.zero_mem
    · exact contained_quotient V _ _ hD (hmax _
        (hPS (Finset.mem_image_of_mem P.coeff (mem_support_iff.mpr hzero))))
  have hA := hAll A (fun _ h => Finset.mem_union_left _ h)
  have hB' := hAll B (fun _ h => Finset.mem_union_right _ h)
  refine ⟨⟨d,hD,normalize V A d hA,normalize V B d hB',
    normalize_scale V A d hD hA,normalize_scale V B d hD hB',
    normalize_natDegree V A d hA,normalize_natDegree V B d hB',?_⟩⟩
  rcases hit with ⟨n,_,e⟩ | ⟨n,_,e⟩
  · exact Or.inl (normalize_primitive V A d hD hA n e)
  · exact Or.inr (normalize_primitive V B d hD hB' n e)

/-- One simultaneous scale for a finite family of polynomial
coefficients, including the four coefficient slots of two elements
of the literal quadratic chart. -/
theorem primitive_family {I : Type*} [Fintype I] (P : I→K[X]) (hP : ∃ i, P i≠0) :
    ∃ (d : K) (Q : I→V[X]), d≠0 ∧
      (∀ i, C d*(Q i).map V.subtype=P i) ∧
      (∀ i, (Q i).natDegree≤(P i).natDegree) ∧
      ∃ i, (Q i).map (residue V)≠0 := by
  classical
  let S := (Finset.univ : Finset I).biUnion (fun i => (P i).support.image (P i).coeff)
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hP
    obtain ⟨n,hn⟩ := support_nonempty.mpr hi
    exact ⟨(P i).coeff n,Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image_of_mem _ hn⟩⟩
  obtain ⟨d,hd,hmax⟩ := Finset.exists_max_image S V.valuation hS
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
  have hd0 : d≠0 := he ▸ mem_support_iff.mp hj
  have hAll (i : I) (n : ℕ) : (P i).coeff n/d∈V := by
    by_cases hzero : (P i).coeff n=0
    · rw [hzero,zero_div]
      exact V.zero_mem
    · exact contained_quotient V _ _ hd0 (hmax _ (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_image_of_mem _ (mem_support_iff.mpr hzero)⟩))
  refine ⟨d,(fun i => normalize V (P i) d (hAll i)),hd0,?_,?_,?_⟩
  · exact fun i => normalize_scale V (P i) d hd0 (hAll i)
  · exact fun i => normalize_natDegree V (P i) d (hAll i)
  · exact ⟨i,normalize_primitive V (P i) d hd0 (hAll i) j he⟩

end ActualGaussianWeberPrimitiveRational318
