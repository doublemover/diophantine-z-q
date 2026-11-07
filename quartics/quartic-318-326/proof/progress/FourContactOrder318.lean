module
public import FourUnitCover318
public import ContactOrder318
public import TensorPairBaseChange318
public section
noncomputable section
namespace FourContactOrder318
set_option maxHeartbeats 900000
open scoped TensorProduct
variable {R:Type*} [CommRing R] (u:Fin 4→Rˣ) (pi:R) (m:Fin 4→ℕ)
abbrev Factor (i:Fin 4):=QuadraticPresentation318.RootRing ((u i:R)*pi^(2*m i))
abbrev Pair01:=Factor u pi m 0⊗[R]Factor u pi m 1
abbrev Pair23:=Factor u pi m 2⊗[R]Factor u pi m 3
abbrev Order:=Pair01 u pi m⊗[R]Pair23 u pi m

@[expose] def pairMap01 : Pair01 u pi m→ₐ[R]FourUnitCover318.Pair01 u :=
  Algebra.TensorProduct.map (ContactBaseChange318.contactMap (u 0) pi (m 0))
    (ContactBaseChange318.contactMap (u 1) pi (m 1))
@[expose] def pairMap23 : Pair23 u pi m→ₐ[R]FourUnitCover318.Pair23 u :=
  Algebra.TensorProduct.map (ContactBaseChange318.contactMap (u 2) pi (m 2))
    (ContactBaseChange318.contactMap (u 3) pi (m 3))
@[expose] def orderMap : Order u pi m→ₐ[R]FourUnitCover318.Cover u :=
  Algebra.TensorProduct.map (pairMap01 u pi m) (pairMap23 u pi m)

theorem finite_free : Module.Finite R (Order u pi m) ∧ Module.Free R (Order u pi m) := by
  letI (i:Fin 4):Module.Finite R (Factor u pi m i):=ContactOrder318.finite_order _ _ _
  letI (i:Fin 4):Module.Free R (Factor u pi m i):=ContactOrder318.free_order _ _ _
  exact ⟨inferInstance,inferInstance⟩

theorem factor_rank_two [Nontrivial R] (i:Fin 4) : Module.finrank R (Factor u pi m i)=2 := by
  have hm:(QuadraticPresentation318.polynomial ((u i:R)*pi^(2*m i))).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by decide : 2≠0)
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hm).basis,Fintype.card_fin]
  change (QuadraticPresentation318.polynomial ((u i:R)*pi^(2*m i))).natDegree=2
  exact Polynomial.natDegree_X_pow_sub_C

theorem rank_sixteen [Nontrivial R] : Module.finrank R (Order u pi m)=16 := by
  letI (i:Fin 4):Module.Free R (Factor u pi m i):=ContactOrder318.free_order _ _ _
  simp only [Order,Pair01,Pair23,Module.finrank_tensorProduct,factor_rank_two]

variable {S:Type*} [CommRing S] [Algebra R S]
@[expose] def genericEquiv (hp:IsUnit (algebraMap R S pi)) :
    S⊗[R]Order u pi m ≃ₐ[S] S⊗[R]FourUnitCover318.Cover u :=
  TensorPairBaseChange318.tensorEquiv
    (TensorPairBaseChange318.tensorEquiv
      (ContactGenericFiber318.genericFiberEquiv (u 0) pi (m 0) hp)
      (ContactGenericFiber318.genericFiberEquiv (u 1) pi (m 1) hp))
    (TensorPairBaseChange318.tensorEquiv
      (ContactGenericFiber318.genericFiberEquiv (u 2) pi (m 2) hp)
      (ContactGenericFiber318.genericFiberEquiv (u 3) pi (m 3) hp))

/-- Compatibility is on every actual order element, not only chosen roots. -/
theorem genericEquiv_on_order (hp:IsUnit (algebraMap R S pi)) (z:Order u pi m) :
    genericEquiv u pi m hp (1⊗ₜ[R]z)=1⊗ₜ[R]orderMap u pi m z := by
  apply TensorPairBaseChange318.tensorEquiv_on_order
  · intro a
    apply TensorPairBaseChange318.tensorEquiv_on_order
    · exact ContactGenericFiber318.genericFiberEquiv_on_order _ _ _ hp
    · exact ContactGenericFiber318.genericFiberEquiv_on_order _ _ _ hp
  · intro b
    apply TensorPairBaseChange318.tensorEquiv_on_order
    · exact ContactGenericFiber318.genericFiberEquiv_on_order _ _ _ hp
    · exact ContactGenericFiber318.genericFiberEquiv_on_order _ _ _ hp

/-- No domain or distinctness assumption on any quadratic factor is made. -/
theorem orderMap_injective [IsDomain R] (hpi:pi≠0) : Function.Injective (orderMap u pi m) := by
  letI:Module.Free R (Order u pi m):=(finite_free u pi m).2
  have hi:=Algebra.TensorProduct.includeRight_injective (R:=R)
    (A:=FractionRing R) (B:=Order u pi m) (IsFractionRing.injective R (FractionRing R))
  have hp:IsUnit (algebraMap R (FractionRing R) pi):=
    IsUnit.mk0 _ (by simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hpi)
  intro a b hab
  apply hi
  apply (genericEquiv u pi m hp).injective
  simpa only [Algebra.TensorProduct.includeRight_apply,genericEquiv_on_order] using
    congrArg (fun z:FourUnitCover318.Cover u=>(1:FractionRing R)⊗ₜ[R]z) hab

end FourContactOrder318
