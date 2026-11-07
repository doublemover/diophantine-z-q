module
public import AffineIntegralModel318
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public section
noncomputable section
namespace FiniteAffineOrder318
set_option maxHeartbeats 0
universe u
variable {R B:Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Elements of the ambient algebra with a denominator-cleared representative
in an actual subalgebra. -/
@[expose] def saturated (d:R) (A:Subalgebra R B) : Subalgebra R B where
  carrier := {b | ∃n:ℕ,algebraMap R B d^n*b∈A}
  zero_mem' := ⟨0,by simp⟩
  one_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro x y ⟨n,hn⟩ ⟨m,hm⟩
    refine ⟨n+m,?_⟩
    have h1:=A.mul_mem (A.pow_mem (A.algebraMap_mem d) m) hn
    have h2:=A.mul_mem (A.pow_mem (A.algebraMap_mem d) n) hm
    convert A.add_mem h1 h2 using 1 <;> ring
  mul_mem' := by
    rintro x y ⟨n,hn⟩ ⟨m,hm⟩
    refine ⟨n+m,?_⟩
    convert A.mul_mem hn hm using 1 <;> ring
  algebraMap_mem' := fun r => ⟨0,by simpa using A.algebraMap_mem r⟩

/-- A finite type algebra whose generators can be cleared to integral elements
has a genuinely finite suborder recovering every element after inverting d. -/
theorem exists_finite_order [Algebra.FiniteType R B] (d:R)
    (hclear:∀b:B,∃n:ℕ,IsIntegral R (algebraMap R B d^n*b)) :
    ∃A:Subalgebra R B,Module.Finite R A ∧
      ∀b:B,∃n:ℕ,algebraMap R B d^n*b∈A := by
  classical
  obtain ⟨s,hs⟩:=Algebra.FiniteType.out (R:=R) (A:=B)
  choose n hn using hclear
  let t:Set B:=(fun b:B=>algebraMap R B d^(n b)*b) '' (s:Set B)
  let A:=Algebra.adjoin R t
  have hA:Module.Finite R A:=Algebra.finite_adjoin_of_finite_of_isIntegral
    (s.finite_toSet.image _) (by rintro _ ⟨b,hb,rfl⟩; exact hn b)
  refine ⟨A,hA,?_⟩
  have ht:Algebra.adjoin R (s:Set B)≤saturated d A:=by
    apply Algebra.adjoin_le
    intro b hb
    exact ⟨n b,Algebra.subset_adjoin ⟨b,hb,rfl⟩⟩
  rw [hs] at ht
  intro b
  exact ht (show b∈(⊤:Subalgebra R B) from trivial)

/-- This recovery is an actual localization of the constructed finite order,
provided the original denominator is already a unit. -/
theorem localization_of_clearing (d:R) (A:Subalgebra R B)
    (hu:IsUnit (algebraMap R B d))
    (hclear:∀b:B,∃n:ℕ,algebraMap R B d^n*b∈A) :
    IsLocalization.Away (algebraMap R A d) B := by
  apply IsLocalization.Away.mk
  · change IsUnit (algebraMap R B d)
    exact hu
  · intro b
    obtain ⟨n,hn⟩:=hclear b
    refine ⟨n,⟨algebraMap R B d^n*b,hn⟩,?_⟩
    change b*algebraMap R B d^n=algebraMap R B d^n*b
    exact mul_comm _ _
  · intro a b hab
    have he:a=b:=Subtype.ext hab
    exact ⟨0,by rw [he]⟩

variable {Rf:Type u} [CommRing Rf] [Algebra R Rf] [Algebra Rf B]
  [IsScalarTower R Rf B] (d:R) [IsLocalization.Away d Rf] [Module.Finite Rf B]

include Rf in
/-- Every genuine finite open-cover algebra admits a finite affine order over
the unlocalized base, with the actual original algebra as its denominator localization. -/
theorem finite_order_of_open_cover :
    ∃A:Subalgebra R B,Module.Finite R A ∧
      IsLocalization.Away (algebraMap R A d) B := by
  let : Algebra.FinitePresentation R Rf:=IsLocalization.Away.finitePresentation d
  let : Algebra.FiniteType R B:=Algebra.FiniteType.trans
    (inferInstance:Algebra.FiniteType R Rf) (inferInstance:Algebra.FiniteType Rf B)
  obtain ⟨A,hA,hclear⟩:=exists_finite_order d
    (AffineIntegralModel318.integral_multiple (Rf:=Rf) (B:=B) d)
  refine ⟨A,hA,localization_of_clearing d A ?_ hclear⟩
  have hu:=(IsLocalization.Away.algebraMap_isUnit (S:=Rf) d).map (algebraMap Rf B)
  simpa only [←IsScalarTower.algebraMap_apply R Rf B] using hu

end FiniteAffineOrder318
