module
public import FourRootOrder318
public import KummerTensorField318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ContactKummerOrder318
set_option maxHeartbeats 500000
open Polynomial
open scoped TensorProduct
open FourRootOrder318
abbrev R:=Polynomial ℚ
abbrev K:=RatFunc ℚ
@[expose] def coefficient (c:Fin 4→ℚˣ) (i:Fin 4) : R :=
  C (c i:ℚ)*(X-C (LinearContactSquareclass318.contacts i))
abbrev SourceOrder (c:Fin 4→ℚˣ):=Order (coefficient c)

theorem source_finite_free (c:Fin 4→ℚˣ) :
    Module.Finite R (SourceOrder c) ∧ Module.Free R (SourceOrder c) := finite_free _
theorem source_rank_sixteen (c:Fin 4→ℚˣ) : Module.finrank R (SourceOrder c)=16 := rank_sixteen _

/-- The exact original four-root polynomial order has the actual constructed
Kummer field as its genuine rational-function base change. -/
@[expose] def genericFiber (c:Fin 4→ℚˣ) :
    K⊗[R]SourceOrder c ≃ₐ[K] KummerTensorField318.Raw (SourceKummerField318.parameter c) :=
  baseChange (coefficient c) K

@[expose] def embedding (c:Fin 4→ℚˣ) :
    SourceOrder c→+*KummerTensorField318.Raw (SourceKummerField318.parameter c) :=
  (genericFiber c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : SourceOrder c→ₐ[R]K⊗[R]SourceOrder c).toRingHom

theorem embedding_injective (c:Fin 4→ℚˣ) : Function.Injective (embedding c) := by
  letI:Module.Free R (SourceOrder c):=(source_finite_free c).2
  exact (genericFiber c).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R:=R) (A:=K) (B:=SourceOrder c)
      (IsFractionRing.injective R K))

theorem source_domain (c:Fin 4→ℚˣ) : IsDomain (SourceOrder c) := by
  letI:Field (KummerTensorField318.Raw (SourceKummerField318.parameter c)):=
    (KummerTensorField318.source_raw_field c).toField
  exact Function.Injective.isDomain (embedding c) (embedding_injective c)

@[expose] def denominator : R := ∏i:Fin 4,(X-C (LinearContactSquareclass318.contacts i))
abbrev OpenBase:=Localization.Away denominator
abbrev OpenOrder (c:Fin 4→ℚˣ):=Order (fun i=>algebraMap R OpenBase (coefficient c i))

theorem denominator_ne_zero : denominator≠0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>Polynomial.X_sub_C_ne_zero _)

instance openBase_domain : IsDomain OpenBase := Localization.Away.isDomain denominator_ne_zero

theorem coefficient_unit (c:Fin 4→ℚˣ) (i:Fin 4) :
    IsUnit (algebraMap R OpenBase (coefficient c i)) := by
  rw [coefficient,map_mul]
  apply IsUnit.mul
  · exact ((c i).isUnit.map C).map (algebraMap R OpenBase)
  · apply IsLocalization.Away.isUnit_of_dvd denominator
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem two_unit : IsUnit (2:OpenBase) := by
  have h:IsUnit (2:ℚ):=IsUnit.mk0 2 (by norm_num)
  simpa only [map_ofNat] using (h.map C).map (algebraMap R OpenBase)

/-- On precisely the complement of the four finite contacts, the original
order is an actual finite-free etale cover of degree sixteen. -/
theorem open_finite_free_etale (c:Fin 4→ℚˣ) :
    Module.Finite OpenBase (OpenOrder c) ∧ Module.Free OpenBase (OpenOrder c) ∧
      Algebra.Etale OpenBase (OpenOrder c) :=
  ⟨(finite_free _).1,(finite_free _).2,etale _ two_unit (coefficient_unit c)⟩

theorem open_rank_sixteen (c:Fin 4→ℚˣ) : Module.finrank OpenBase (OpenOrder c)=16 := rank_sixteen _

theorem open_faithfullyFlat (c:Fin 4→ℚˣ) : Module.FaithfullyFlat OpenBase (OpenOrder c) :=
  faithfullyFlat _

@[expose] def openBaseChange (c:Fin 4→ℚˣ) :
    OpenBase⊗[R]SourceOrder c≃ₐ[OpenBase]OpenOrder c := baseChange _ _
end ContactKummerOrder318
