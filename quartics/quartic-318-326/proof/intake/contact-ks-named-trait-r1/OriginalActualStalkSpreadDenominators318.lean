module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
noncomputable section

namespace OriginalActualStalkSpreadDenominators318

open scoped BigOperators

variable {A Q : Type*} [CommRing A] [CommRing Q] [Algebra A Q]
variable (P : Ideal A) [P.IsPrime] [IsLocalization P.primeCompl Q]
variable (t : A) (ht : t ∈ P.primeCompl)

def toStalk : Localization.Away t→ₐ[A]Q :=
  IsLocalization.Away.liftAlgHom t (f:=Algebra.ofId A Q)
    (IsLocalization.map_units Q ⟨t,ht⟩)

theorem toStalk_injective [IsDomain A] : Function.Injective (toStalk (Q:=Q) P t ht) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (.powers t)
    (toStalk (Q:=Q) P t ht).toRingHom).2
  intro x y
  change _ = _ ↔ toStalk (Q:=Q) P t ht (algebraMap A (Localization.Away t) x) =
    toStalk (Q:=Q) P t ht (algebraMap A (Localization.Away t) y)
  rw [AlgHom.commutes,AlgHom.commutes]
  have ht0 : t≠0 := fun e=>ht (by simpa [e] using (P.zero_mem : (0:A)∈P))
  exact (IsLocalization.injective (Localization.Away t)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)).eq_iff.trans
      (IsLocalization.injective Q P.primeCompl_le_nonZeroDivisors).eq_iff.symm

variable {ι : Type*} [Fintype ι]

/-- Spread finitely many *given actual stalk values* to one
principal open through the named point.  The map back to the stalk
is injective on the entire new affine ring. -/
theorem actual_finite_denominators (values : ι→Q) :
    ∃ (t : A) (ht : t ∈ P.primeCompl) (f : ι→Localization.Away t),
      ∀ i,toStalk (Q:=Q) P t ht (f i)=values i := by
  classical
  choose e he using fun i => IsLocalization.surj P.primeCompl (values i)
  let t := ∏ i, ((e i).2:A)
  have ht : t ∈ P.primeCompl := P.primeCompl.prod_mem (fun i _ => (e i).2.property)
  let w (i : ι) : (Localization.Away t)ˣ :=
    (IsLocalization.Away.isUnit_of_dvd (S:=Localization.Away t) t
      (Finset.dvd_prod_of_mem (fun i => ((e i).2:A)) (Finset.mem_univ i))).unit
  refine ⟨t,ht,fun i => algebraMap A (Localization.Away t) (e i).1 *
    ((w i)⁻¹:(Localization.Away t)ˣ),?_⟩
  intro i
  let f := toStalk (Q:=Q) P t ht
  have h (a : A) : f (algebraMap A (Localization.Away t) a)=algebraMap A Q a :=
    f.commutes a
  have uw : ((w i: (Localization.Away t)ˣ):Localization.Away t)=
      algebraMap A (Localization.Away t) ((e i).2:A) :=
    IsUnit.unit_spec _
  have add : f ((w i: (Localization.Away t)ˣ):Localization.Away t)=
    algebraMap A Q ((e i).2:A) := by rw [uw,h]
  change f (algebraMap A (Localization.Away t) (e i).1 *
    (((w i)⁻¹:(Localization.Away t)ˣ):Localization.Away t))=_
  calc
    _ = f (algebraMap A (Localization.Away t) (e i).1) *
        f (((w i)⁻¹:(Localization.Away t)ˣ):Localization.Away t) := map_mul _ _ _
    _ = (values i * f ((w i: (Localization.Away t)ˣ):Localization.Away t)) *
        f (((w i)⁻¹:(Localization.Away t)ˣ):Localization.Away t) := by rw [h,←he i,add]
    _ = _ := by
      rw [mul_assoc,←map_mul,Units.mul_inv,map_one,mul_one]

end OriginalActualStalkSpreadDenominators318
