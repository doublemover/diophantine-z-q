module
public import VaryingCommutingMatrixRing318
public section
noncomputable section
namespace VaryingCommutingMatrixPoints318
open VaryingCommutingMatrixRing318
universe u
variable (R σ ι : Type u) [CommRing R] [Fintype ι]
variable (S : Type u) [CommRing S] [Algebra R S]

@[expose] def forward (f : algebra R σ ι →ₐ[R] S) : Data σ ι S where
  matrices := fun s i j => f (quotient R σ ι (MvPolynomial.X (Sum.inl (s,i,j))))
  marked := fun i => f (quotient R σ ι (MvPolynomial.X (Sum.inr i)))
  commute := by
    intro s t
    ext i j
    apply sub_eq_zero.mp
    change (∑ k, f (quotient R σ ι (MvPolynomial.X (Sum.inl (s,i,k)))) *
      f (quotient R σ ι (MvPolynomial.X (Sum.inl (t,k,j))))) -
      (∑ k, f (quotient R σ ι (MvPolynomial.X (Sum.inl (t,i,k)))) *
      f (quotient R σ ι (MvPolynomial.X (Sum.inl (s,k,j)))))=0
    have h := congrArg f (relation_zero R σ ι (s,t,i,j))
    simpa only [relation,matrix,Matrix.mul_apply,map_sub,map_sum,map_mul,map_zero] using h

@[expose] def backward (d : Data σ ι S) : algebra R σ ι →ₐ[R] S :=
  Ideal.Quotient.liftₐ (ideal R σ ι) (evaluate R σ ι S d)
    (fun a ha => RingHom.mem_ker.mp (ideal_le_kernel R σ ι S d ha))

lemma backward_variable (d : Data σ ι S) (x : Variable σ ι) :
    backward R σ ι S d (quotient R σ ι (MvPolynomial.X x)) = d.values x := by
  have h := congrArg (fun f : polynomial R σ ι →ₐ[R] S => f (MvPolynomial.X x))
    (Ideal.Quotient.liftₐ_comp (ideal R σ ι) (evaluate R σ ι S d)
      (fun a ha => RingHom.mem_ker.mp (ideal_le_kernel R σ ι S d ha)))
  exact h.trans (MvPolynomial.aeval_X d.values x)

/-- The explicit polynomial quotient represents commuting matrices and
one marked vector on ALL coefficient algebra tests. It is not a set of
geometric points; both inverse maps retain every quotient relation. -/
@[expose] def points : (algebra R σ ι →ₐ[R] S) ≃ Data σ ι S where
  toFun := forward R σ ι S
  invFun := backward R σ ι S
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro x
    change backward R σ ι S (forward R σ ι S f)
      (quotient R σ ι (MvPolynomial.X x))=f (quotient R σ ι (MvPolynomial.X x))
    rw [backward_variable]
    cases x <;> rfl
  right_inv d := by
    apply Data.ext
    · funext s i j
      exact backward_variable R σ ι S d (Sum.inl (s,i,j))
    · funext i
      exact backward_variable R σ ι S d (Sum.inr i)

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)

/-- Coefficient change applies the SAME homomorphism to every matrix
entry and vector coordinate; commutation survives as an exact equality. -/
@[expose] def mapData (d : Data σ ι S) : Data σ ι T where
  matrices := fun s i j => f (d.matrices s i j)
  marked := fun i => f (d.marked i)
  commute := by
    intro s t
    ext i j
    change (∑ k, f (d.matrices s i k) * f (d.matrices t k j))=
      (∑ k, f (d.matrices t i k) * f (d.matrices s k j))
    have h := congrArg f (congrFun (congrFun (d.commute s t) i) j)
    simpa only [Matrix.mul_apply,map_sum,map_mul] using h

lemma forward_natural (a : algebra R σ ι →ₐ[R] S) :
    forward R σ ι T (f.comp a)=mapData R σ ι S T f (forward R σ ι S a) := by
  apply Data.ext <;> rfl
end VaryingCommutingMatrixPoints318
