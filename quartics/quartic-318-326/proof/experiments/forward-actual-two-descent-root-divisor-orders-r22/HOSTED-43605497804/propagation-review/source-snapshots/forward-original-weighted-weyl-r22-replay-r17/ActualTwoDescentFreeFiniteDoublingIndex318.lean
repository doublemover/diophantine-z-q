module
public import ActualTwoDescentDoublingIndexTransport318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace ActualTwoDescentFreeFiniteDoublingIndex318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentDoublingIndexTransport318

lemma actual_free_doubles_index (r : ℕ) : (doubles (Fin r →₀ ℤ)).index=2^r := by
  simpa only [Module.finrank_finsupp_self,Fintype.card_fin] using
    AddSubgroup.index_range_nsmul (Fin r →₀ ℤ) 2

lemma actual_free_double_kernel_card (r : ℕ) : Nat.card (doubleKernel (Fin r →₀ ℤ))=1 := by
  have hz : ∀ a : doubleKernel (Fin r →₀ ℤ), a.val=0 := by
    intro a
    ext i
    have h := congrArg (fun f : Fin r →₀ ℤ => f i) a.property
    have h' : a.val i+a.val i=0 := by
      simpa only [nsmulAddMonoidHom_apply,two_nsmul,Finsupp.add_apply,Finsupp.zero_apply] using h
    change a.val i=0
    omega
  letI : Subsingleton (doubleKernel (Fin r →₀ ℤ)) := ⟨fun a b => Subtype.ext ((hz a).trans (hz b).symm)⟩
  exact Nat.card_unique

lemma actual_finite_doubles_index (T : Type*) [AddCommGroup T] [Finite T] :
    (doubles T).index=Nat.card (doubleKernel T) := by
  letI : (doubleKernel T).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact AddSubgroup.index_range

/-- For an ACTUAL group decomposition, the doubling index is the free
power of two times the actual two-torsion cardinality. -/
theorem actual_free_finite_index {A : Type*} [AddCommGroup A] (r : ℕ)
    (T : Type*) [AddCommGroup T] [Finite T] (e : A ≃+ (Fin r →₀ ℤ) × T) :
    (doubles A).index=2^r*Nat.card (doubleKernel A) := by
  have hk : Nat.card (doubleKernel A)=Nat.card (doubleKernel T) := by
    rw [Nat.card_congr (doubleKernelEquiv e),Nat.card_congr (doubleKernelProdEquiv (A:=Fin r →₀ ℤ) (B:=T)),Nat.card_prod,
      actual_free_double_kernel_card,one_mul]
  rw [actual_doubles_index_equiv e,actual_doubles_prod,AddSubgroup.index_prod,
    actual_free_doubles_index,actual_finite_doubles_index,hk]

end ActualTwoDescentFreeFiniteDoublingIndex318
