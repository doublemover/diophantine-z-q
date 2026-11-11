module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace VaryingCommutingMatrixRing318
universe u
variable (R σ ι : Type u) [CommRing R] [Fintype ι]

abbrev Variable := (σ × ι × ι) ⊕ ι
abbrev polynomial := MvPolynomial (Variable σ ι) R

@[expose] def matrix (s : σ) : Matrix ι ι (polynomial R σ ι) :=
  fun i j => MvPolynomial.X (Sum.inl (s,i,j))
@[expose] def vector : ι → polynomial R σ ι := fun i => MvPolynomial.X (Sum.inr i)

/-- Literal entries of the universal commutators. All entries are
relations, including off-diagonal entries over nonreduced test rings. -/
@[expose] def relation (t : σ × σ × ι × ι) : polynomial R σ ι :=
  (matrix R σ ι t.1 * matrix R σ ι t.2.1) t.2.2.1 t.2.2.2 -
    (matrix R σ ι t.2.1 * matrix R σ ι t.1) t.2.2.1 t.2.2.2
@[expose] def ideal : Ideal (polynomial R σ ι) := Ideal.span (Set.range (relation R σ ι))
abbrev algebra := polynomial R σ ι ⧸ ideal R σ ι
abbrev quotient : polynomial R σ ι →ₐ[R] algebra R σ ι :=
  Ideal.Quotient.mkₐ R (ideal R σ ι)

lemma relation_zero (t : σ × σ × ι × ι) : quotient R σ ι (relation R σ ι t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self t))

/-- Actual commuting matrices with a marked vector over a test ring.
Cyclicity and source-algebra relation equations are separate restrictions. -/
structure Data (S : Type u) [CommRing S] where
  matrices : σ → Matrix ι ι S
  marked : ι → S
  commute : ∀ s t, matrices s * matrices t = matrices t * matrices s

variable {R σ ι}
@[ext] lemma Data.ext {S : Type u} [CommRing S] {a b : Data σ ι S}
    (hm : a.matrices=b.matrices) (hv : a.marked=b.marked) : a=b := by
  cases a
  cases b
  cases hm
  cases hv
  rfl

@[expose] def Data.values {S : Type u} [CommRing S] (d : Data σ ι S) : Variable σ ι → S :=
  Sum.elim (fun t => d.matrices t.1 t.2.1 t.2.2) d.marked

variable (R σ ι) (S : Type u) [CommRing S] [Algebra R S]
@[expose] def evaluate (d : Data σ ι S) : polynomial R σ ι →ₐ[R] S :=
  MvPolynomial.aeval d.values

lemma evaluate_relation (d : Data σ ι S) (t : σ × σ × ι × ι) :
    evaluate R σ ι S d (relation R σ ι t)=0 := by
  simp only [evaluate,relation,matrix,Matrix.mul_apply,map_sub,map_sum,map_mul,
    MvPolynomial.aeval_X,Data.values,Sum.elim_inl]
  exact sub_eq_zero.mpr (congrFun (congrFun (d.commute t.1 t.2.1) t.2.2.1) t.2.2.2)

lemma ideal_le_kernel (d : Data σ ι S) :
    ideal R σ ι ≤ RingHom.ker (evaluate R σ ι S d).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨t,rfl⟩
  change evaluate R σ ι S d (relation R σ ι t)=0
  exact evaluate_relation R σ ι S d t
end VaryingCommutingMatrixRing318
