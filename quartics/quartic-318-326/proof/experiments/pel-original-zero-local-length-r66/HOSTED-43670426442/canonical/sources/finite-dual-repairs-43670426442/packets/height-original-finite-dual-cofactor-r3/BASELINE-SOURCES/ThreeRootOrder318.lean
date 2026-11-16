module
public import FourRootOrder318
public section
noncomputable section
namespace ThreeRootOrder318
set_option maxHeartbeats 500000
open scoped TensorProduct
open QuadraticPresentation318
variable {R:Type*} [CommRing R] (a:Fin 3→R)
abbrev Pair12:=RootRing (a 1)⊗[R]RootRing (a 2)
abbrev Order:=RootRing (a 0)⊗[R]Pair12 a

theorem finite_free : Module.Finite R (Order a) ∧ Module.Free R (Order a) := by
  letI (i:Fin 3):Module.Finite R (RootRing (a i)):=FourRootOrder318.root_finite _
  letI (i:Fin 3):Module.Free R (RootRing (a i)):=FourRootOrder318.root_free _
  exact ⟨inferInstance,inferInstance⟩

theorem rank_eight [Nontrivial R] : Module.finrank R (Order a)=8 := by
  letI (i:Fin 3):Module.Free R (RootRing (a i)):=FourRootOrder318.root_free _
  simp only [Order,Pair12,Module.finrank_tensorProduct,FourRootOrder318.root_rank]

theorem faithfullyFlat [Nontrivial R] : Module.FaithfullyFlat R (Order a) := by
  letI:Module.Free R (Order a):=(finite_free a).2
  letI:Nontrivial (Order a):=Module.nontrivial_of_finrank_pos (R:=R) (by rw [rank_eight];decide)
  infer_instance

theorem etale (h2:IsUnit (2:R)) (ha:∀i,IsUnit (a i)) : Algebra.Etale R (Order a) := by
  letI (i:Fin 3):Algebra.Etale R (RootRing (a i)):=by
    letI:Algebra.Etale R (RootRing ((ha i).unit:R)):=
      EvenContactEtale318.rootRing_etale (ha i).unit h2
    exact Algebra.Etale.of_equiv (ContactGenericFiber318.rootParameterEquiv (ha i).unit_spec)
  letI:Algebra.Etale R (Pair12 a):=Algebra.Etale.comp R (RootRing (a 1)) (Pair12 a)
  exact Algebra.Etale.comp R (RootRing (a 0)) (Order a)

variable (S:Type*) [CommRing S] [Algebra R S]
@[expose] def baseChange : S⊗[R]Order a≃ₐ[S]Order (fun i=>algebraMap R S (a i)) :=
  (TensorPairBaseChange318.merge R S (RootRing (a 0)) (Pair12 a)).symm.trans
    (Algebra.TensorProduct.congr (ContactGenericFiber318.rootBaseChange (a 0))
      (FourRootOrder318.pairBaseChange S (a 1) (a 2)))

/-- Regroup the actual fourfold tensor order around its first root factor. -/
@[expose] def fourRootRegroup (b:Fin 4→R) :
    FourRootOrder318.Order b ≃ₐ[R]
      RootRing (b 0)⊗[R]Order (fun i=>b i.succ) :=
  Algebra.TensorProduct.assoc R R R (RootRing (b 0)) (RootRing (b 1))
    (RootRing (b 2)⊗[R]RootRing (b 3))
end ThreeRootOrder318
