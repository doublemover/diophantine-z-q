module
public import TensorPairBaseChange318
public import ContactGenericFiber318
public import EvenContactEtale318
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace FourRootOrder318
set_option maxHeartbeats 500000
open scoped TensorProduct
open QuadraticPresentation318
variable {R:Type*} [CommRing R] (a:Fin 4→R)
abbrev Pair01:=RootRing (a 0)⊗[R]RootRing (a 1)
abbrev Pair23:=RootRing (a 2)⊗[R]RootRing (a 3)
abbrev Order:=Pair01 a⊗[R]Pair23 a

theorem root_finite (r:R) : Module.Finite R (RootRing r) :=
  (Polynomial.monic_X_pow_sub_C r (by decide : 2≠0)).finite_adjoinRoot

theorem root_free (r:R) : Module.Free R (RootRing r) :=
  (Polynomial.monic_X_pow_sub_C r (by decide : 2≠0)).free_adjoinRoot

theorem finite_free : Module.Finite R (Order a) ∧ Module.Free R (Order a) := by
  letI (i:Fin 4):Module.Finite R (RootRing (a i)):=root_finite _
  letI (i:Fin 4):Module.Free R (RootRing (a i)):=root_free _
  exact ⟨inferInstance,inferInstance⟩

theorem root_rank [Nontrivial R] (r:R) : Module.finrank R (RootRing r)=2 := by
  have hm:(polynomial r).Monic:=Polynomial.monic_X_pow_sub_C r (by decide : 2≠0)
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hm).basis,Fintype.card_fin]
  exact Polynomial.natDegree_X_pow_sub_C

theorem rank_sixteen [Nontrivial R] : Module.finrank R (Order a)=16 := by
  letI (i:Fin 4):Module.Free R (RootRing (a i)):=root_free _
  simp only [Order,Pair01,Pair23,Module.finrank_tensorProduct,root_rank]

theorem faithfullyFlat [Nontrivial R] : Module.FaithfullyFlat R (Order a) := by
  letI:Module.Free R (Order a):=(finite_free a).2
  letI:Nontrivial (Order a):=Module.nontrivial_of_finrank_pos (R:=R) (by rw [rank_sixteen];decide)
  infer_instance

theorem etale (h2:IsUnit (2:R)) (ha:∀i,IsUnit (a i)) : Algebra.Etale R (Order a) := by
  letI (i:Fin 4):Algebra.Etale R (RootRing (a i)):=by
    letI:Algebra.Etale R (RootRing ((ha i).unit:R)):=
      EvenContactEtale318.rootRing_etale (ha i).unit h2
    exact Algebra.Etale.of_equiv (ContactGenericFiber318.rootParameterEquiv (ha i).unit_spec)
  letI:Algebra.Etale R (Pair01 a):=Algebra.Etale.comp R (RootRing (a 0)) (Pair01 a)
  letI:Algebra.Etale R (Pair23 a):=Algebra.Etale.comp R (RootRing (a 2)) (Pair23 a)
  exact Algebra.Etale.comp R (Pair01 a) (Order a)

variable (S:Type*) [CommRing S] [Algebra R S]
@[expose] def pairBaseChange (b c:R) :
    S⊗[R](RootRing b⊗[R]RootRing c) ≃ₐ[S]
      RootRing (algebraMap R S b)⊗[S]RootRing (algebraMap R S c) :=
  (TensorPairBaseChange318.merge R S (RootRing b) (RootRing c)).symm.trans
    (Algebra.TensorProduct.congr (ContactGenericFiber318.rootBaseChange b)
      (ContactGenericFiber318.rootBaseChange c))

/-- Actual base change of all four polynomial quotients. -/
@[expose] def baseChange : S⊗[R]Order a≃ₐ[S]Order (fun i=>algebraMap R S (a i)) :=
  (TensorPairBaseChange318.merge R S (Pair01 a) (Pair23 a)).symm.trans
    (Algebra.TensorProduct.congr (pairBaseChange S (a 0) (a 1))
      (pairBaseChange S (a 2) (a 3)))
end FourRootOrder318
