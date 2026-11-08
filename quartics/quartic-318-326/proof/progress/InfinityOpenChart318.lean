module
public import TripleQuadraticField318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace InfinityOpenChart318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
variable (c:Fin 4→ℚˣ)
abbrev R:=ℚ[X]
abbrev K:=RatFunc ℚ
abbrev Order:=ThreeRootOrder318.Order (InfinityParameters318.coefficient c)
@[expose] def denominator : R := ∏j:Fin 3,InfinityParameters318.coefficient c j
abbrev OpenBase:=Localization.Away (denominator c)
abbrev OpenOrder:=ThreeRootOrder318.Order
  (fun j=>algebraMap R (OpenBase c) (InfinityParameters318.coefficient c j))

@[expose] def genericFiber : K⊗[R]Order c≃ₐ[K]
    TripleQuadraticField318.Raw (InfinityParameters318.parameter c) :=
  ThreeRootOrder318.baseChange _ K
@[expose] def embedding : Order c→+*
    TripleQuadraticField318.Raw (InfinityParameters318.parameter c) :=
  (genericFiber c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Order c→ₐ[R]K⊗[R]Order c).toRingHom

theorem embedding_injective : Function.Injective (embedding c) := by
  letI:Module.Free R (Order c):=(ThreeRootOrder318.finite_free _).2
  exact (genericFiber c).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R:=R) (A:=K) (B:=Order c)
      (IsFractionRing.injective R K))
theorem order_domain : IsDomain (Order c) := by
  letI:Field (TripleQuadraticField318.Raw (InfinityParameters318.parameter c)):=
    (TripleQuadraticField318.infinity_field c).toField
  exact Function.Injective.isDomain (embedding c) (embedding_injective c)

theorem denominator_at_zero :
    Polynomial.eval 0 (denominator c)=∏j:Fin 3,(c j.succ:ℚ)/(c 0:ℚ) := by
  simp only [denominator,Polynomial.eval_prod,InfinityParameters318.coefficient_at_zero]
theorem denominator_at_zero_ne_zero : Polynomial.eval 0 (denominator c)≠0 := by
  rw [denominator_at_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>div_ne_zero (c j.succ).ne_zero (c 0).ne_zero)
theorem denominator_ne_zero : denominator c≠0 := by
  intro h
  exact denominator_at_zero_ne_zero c (by rw [h,Polynomial.eval_zero])
instance openBase_domain : IsDomain (OpenBase c):=Localization.Away.isDomain (denominator_ne_zero c)

/-- The infinity coordinate u=0 really belongs to this open base. -/
@[expose] def infinityPoint : OpenBase c→+*ℚ :=
  IsLocalization.Away.lift (g:=Polynomial.evalRingHom 0) (denominator c)
    (IsUnit.mk0 _ (denominator_at_zero_ne_zero c))
@[simp] theorem infinityPoint_on_base (p:R) :
    infinityPoint c (algebraMap R (OpenBase c) p)=Polynomial.eval 0 p :=
  IsLocalization.Away.lift_eq _ _ _

theorem coefficient_unit (j:Fin 3) :
    IsUnit (algebraMap R (OpenBase c) (InfinityParameters318.coefficient c j)) :=
  IsLocalization.Away.isUnit_of_dvd (denominator c)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
theorem two_unit : IsUnit (2:OpenBase c) := by
  have h:IsUnit (2:ℚ):=IsUnit.mk0 2 (by norm_num)
  simpa only [map_ofNat] using (h.map C).map (algebraMap R (OpenBase c))

theorem finite_free_etale_rank_eight :
    Module.Finite (OpenBase c) (OpenOrder c) ∧
    Module.Free (OpenBase c) (OpenOrder c) ∧
    Algebra.Etale (OpenBase c) (OpenOrder c) ∧
    Module.finrank (OpenBase c) (OpenOrder c)=8 ∧
    Module.FaithfullyFlat (OpenBase c) (OpenOrder c) :=
  ⟨(ThreeRootOrder318.finite_free _).1,(ThreeRootOrder318.finite_free _).2,
    ThreeRootOrder318.etale _ (two_unit c) (coefficient_unit c),
    ThreeRootOrder318.rank_eight _,ThreeRootOrder318.faithfullyFlat _⟩

@[expose] def openBaseChange : OpenBase c⊗[R]Order c≃ₐ[OpenBase c]OpenOrder c :=
  ThreeRootOrder318.baseChange _ _

theorem openOrder_domain : IsDomain (OpenOrder c) := by
  letI:IsDomain (Order c):=order_domain c
  letI:Module.Free R (Order c):=(ThreeRootOrder318.finite_free _).2
  letI:Module.FaithfullyFlat R (Order c):=ThreeRootOrder318.faithfullyFlat _
  have hi:Function.Injective (algebraMap R (Order c)):=
    FaithfulSMul.algebraMap_injective R (Order c)
  have hd:algebraMap R (Order c) (denominator c)≠0 := by
    simpa only [map_zero] using hi.ne (denominator_ne_zero c)
  letI:IsLocalization.Away (algebraMap R (Order c) (denominator c))
      (Order c⊗[R]OpenBase c) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (Order c)
        (Submonoid.powers (denominator c))) (Order c⊗[R]OpenBase c))
  letI:IsDomain (Order c⊗[R]OpenBase c):=IsLocalization.Away.isDomain (Order c⊗[R]OpenBase c) hd
  let e:OpenOrder c≃+*(Order c⊗[R]OpenBase c):=
    (openBaseChange c).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm R (OpenBase c) (Order c)).toRingEquiv
  exact Function.Injective.isDomain e e.injective
end InfinityOpenChart318
