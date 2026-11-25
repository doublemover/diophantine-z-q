module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Operations
public section
noncomputable section

namespace OriginalR47RetainedDenominatorSpread318

open Algebra BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] [IsDomain R]
variable (p : Ideal R) [p.IsPrime]

/-- The canonical map from the actual principal open to the local
ring of the fixed arithmetic point. -/
@[expose] def canonical (d : R) (hd : d ∉ p) :
    Localization.Away d →ₐ[R] Localization.AtPrime p := by
  let h : Submonoid.powers d ≤ Submonoid.comap (RingHom.id R) p.primeCompl :=
    Submonoid.powers_le.mpr hd
  refine ⟨IsLocalization.map (Localization.AtPrime p) (RingHom.id R) h,?_⟩
  intro x
  exact IsLocalization.map_eq h x

theorem canonical_injective (d : R) (hd : d ∉ p) :
    Function.Injective (canonical p d hd) := by
  let h : Submonoid.powers d ≤ Submonoid.comap (RingHom.id R) p.primeCompl :=
    Submonoid.powers_le.mpr hd
  change Function.Injective (IsLocalization.map (Localization.AtPrime p) (RingHom.id R) h :
    Localization.Away d →+* Localization.AtPrime p)
  exact IsLocalization.map_injective_of_injective' (Submonoid.powers d) R
    (Localization.AtPrime p) h
    (show (0 : R) ∉ p.primeCompl from fun hz => hz p.zero_mem)
    (Function.injective_id : Function.Injective (RingHom.id R))

variable {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

/-- Clear only finitely many denominators of the literal stalk arrow:
the same principal open neighbourhood then carries the whole arrow.
No finite presentation is assumed, since all relations can be tested
in the faithfully embedded domain localization. -/
theorem spread (f : A →ₐ[R] Localization.AtPrime p) :
    ∃ (d : R) (hd : d ∉ p) (g : A →ₐ[R] Localization.Away d),
      (canonical p d hd).comp g = f := by
  classical
  obtain ⟨S,hS⟩ := Algebra.FiniteType.out (R := R) (A := A)
  have Hex (x : S) := IsLocalization.exists_mk'_eq p.primeCompl (f x)
  choose a b H using Hex
  let d : R := ∏ x : S, (b x : R)
  have hd : d ∉ p := by
    intro hh
    change (∏ x : S, (b x : R)) ∈ p at hh
    obtain ⟨x,_,hx⟩ := Ideal.IsPrime.prod_mem_iff.mp hh
    exact (b x).property hx
  let e : Localization.Away d →ₐ[R] Localization.AtPrime p := canonical p d hd
  have he : Function.Injective e := canonical_injective p d hd
  have hgen (x : S) : f x ∈ e.range := by
    have hdiv : (b x : R) ∣ d := Finset.dvd_prod_of_mem (fun y : S => (b y : R)) (Finset.mem_univ x)
    obtain ⟨c,hc⟩ := hdiv
    let z : Submonoid.powers d := ⟨d,Submonoid.mem_powers _⟩
    let m := IsLocalization.mk' (Localization.Away d) (a x * c) z
    refine ⟨m,?_⟩
    have ha : e m * algebraMap R (Localization.AtPrime p) d =
        algebraMap R (Localization.AtPrime p) (a x * c) := by
      have hM := congrArg e (IsLocalization.mk'_spec (Localization.Away d) (a x * c) z)
      simpa only [map_mul, AlgHom.commutes] using hM
    have hf : f x * algebraMap R (Localization.AtPrime p) d =
        algebraMap R (Localization.AtPrime p) (a x * c) := by
      rw [hc, map_mul, ← mul_assoc, ← H x, IsLocalization.mk'_spec, map_mul]
    exact (IsLocalization.map_units (Localization.AtPrime p) (⟨d,hd⟩ : p.primeCompl)).mul_left_inj.mp
      (ha.trans hf.symm)
  have htop : (⊤ : Subalgebra R A) ≤ e.range.comap f := by
    rw [← hS, Algebra.adjoin_le_iff]
    intro x hx
    exact hgen ⟨x,hx⟩
  let fe : A →ₐ[R] e.range := f.codRestrict e.range fun x => htop (show x ∈ (⊤ : Subalgebra R A) from trivial)
  let EI := AlgEquiv.ofInjective e he
  let g : A →ₐ[R] Localization.Away d := EI.symm.toAlgHom.comp fe
  refine ⟨d,hd,g,?_⟩
  ext x
  change e (EI.symm (fe x)) = f x
  exact congrArg Subtype.val (EI.apply_symm_apply (fe x))

end OriginalR47RetainedDenominatorSpread318

#print axioms OriginalR47RetainedDenominatorSpread318.canonical_injective
#print axioms OriginalR47RetainedDenominatorSpread318.spread
