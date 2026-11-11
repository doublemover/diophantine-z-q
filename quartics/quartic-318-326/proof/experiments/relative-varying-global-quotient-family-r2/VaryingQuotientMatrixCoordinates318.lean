module
public import VaryingCommutingMatrixPoints318
public import CyclicQuotientMatrices318
public section
noncomputable section
namespace VaryingQuotientMatrixCoordinates318
open VaryingCommutingMatrixRing318 VaryingCommutingMatrixPoints318
universe u
variable {S A M σ ι : Type u} [CommRing S]
  [CommRing A] [Algebra S A] [AddCommGroup M] [Module S M]
  [Fintype ι] [DecidableEq ι]
variable (ρ : A →ₐ[S] Module.End S M) (v : M) (b : Basis ι S M) (g : σ → A)

/-- The actual original action yields a point of the commuting-matrix
parameter by taking the specified original source elements in one basis.
No generator completeness or source-relation factorization is asserted. -/
@[expose] def data : Data σ ι S where
  matrices := fun s => CyclicQuotientMatrices318.matrix ρ b (g s)
  marked := CyclicQuotientMatrices318.vector v b
  commute := fun s t => CyclicQuotientMatrices318.matrix_commute ρ b (g s) (g t)

variable (R : Type u) [CommRing R] [Algebra R S]

/-- The map is an ACTUAL algebra map from the represented coordinate
ring, not a geometric-point assignment. Test coefficients may be nilpotent. -/
@[expose] def parameter : algebra R σ ι →ₐ[R] S :=
  backward R σ ι S (data ρ v b g)

lemma parameter_matrix (s : σ) (i j : ι) :
    parameter (R := R) ρ v b g
      (quotient R σ ι (MvPolynomial.X (Sum.inl (s,i,j)))) =
      CyclicQuotientMatrices318.matrix ρ b (g s) i j :=
  backward_variable R σ ι S (data ρ v b g) (Sum.inl (s,i,j))

lemma parameter_vector (i : ι) :
    parameter (R := R) ρ v b g
      (quotient R σ ι (MvPolynomial.X (Sum.inr i))) = b.repr v i :=
  backward_variable R σ ι S (data ρ v b g) (Sum.inr i)
end VaryingQuotientMatrixCoordinates318
