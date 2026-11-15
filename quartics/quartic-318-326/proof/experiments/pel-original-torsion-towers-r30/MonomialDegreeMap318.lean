module
public import MonomialDegreeExhaustion318
public section
noncomputable section
namespace MonomialDegreeMap318
open PurePowerReductionFiniteSpan318 MonomialDegreeFiltration318
variable {ι R A B : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

lemma map_monomial (f : A →ₐ[R] B) (x : ι → A) (d : ι → ℕ) :
    f (monomial x d) = monomial (fun i => f (x i)) d := by
  simp only [monomial,map_prod,map_pow]

/-- Literal algebra homomorphisms preserve the same numerical total
monomial degree, allowing bounds to be chosen in the polynomial base
before any intermediate subalgebra or new normalization is introduced. -/
theorem map_mem (f : A →ₐ[R] B) (x : ι → A) {n : ℕ} {a : A}
    (ha : a ∈ piece (R:=R) x n) :
    f a ∈ piece (R:=R) (fun i => f (x i)) n := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨d,hd,rfl⟩ := ha
    exact Submodule.subset_span ⟨d,hd,(map_monomial f x d).symm⟩
  | zero => simpa only [map_zero] using (piece (R:=R) (fun i => f (x i)) n).zero_mem
  | add a b ha hb ha' hb' =>
    simpa only [map_add] using (piece (fun i => f (x i)) n).add_mem ha' hb'
  | smul r a ha ha' =>
    simpa only [map_smul] using (piece (fun i => f (x i)) n).smul_mem r ha'
end MonomialDegreeMap318
