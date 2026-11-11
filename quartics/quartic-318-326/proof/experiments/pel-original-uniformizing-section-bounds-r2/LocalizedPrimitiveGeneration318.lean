module
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace LocalizedPrimitiveGeneration318
open Algebra
variable (C R A B L:Type*) [CommRing C] [CommRing R] [CommRing A] [CommRing B] [CommRing L]
  [Algebra C A] [Algebra C B] [Algebra C L] [Algebra R A] [Algebra R B] [Algebra R L]
  [Algebra A L] [Algebra B L]
  [IsScalarTower C A L] [IsScalarTower C B L]
  [IsScalarTower R A L] [IsScalarTower R B L]
variable (d:R) [IsLocalization.Away d B]
  [IsLocalization.Away (algebraMap R A d) L]
/-- Full original algebra generators, together with the inverse of the
BASE denominator, generate the ENTIRE source localization. Thus genuine
primitive polynomial expressions for those generators prove equality
of the whole localized order, not just equality of its fraction field.
The generator-expression premises are explicit and must be produced. -/
theorem adjoin_eq_top (s:Finset A)(hs:Algebra.adjoin C (s:Set A)=⊤)(β:L)
    (hg:∀a∈s,algebraMap A L a∈Algebra.adjoin B ({β}:Set L)):
    Algebra.adjoin B ({β}:Set L)=⊤:=by
  let T:=Algebra.adjoin B ({β}:Set L)
  have hle:Algebra.adjoin C (s:Set A)≤
      (T.restrictScalars C).comap (IsScalarTower.toAlgHom C A L):=by
    apply Algebra.adjoin_le
    intro a ha
    exact hg a ha
  have hA(a:A):algebraMap A L a∈T:=by
    apply hle
    rw [hs]
    trivial
  let c:B:=IsLocalization.Away.invSelf d
  have hc:algebraMap R B d*c=1:=IsLocalization.Away.mul_invSelf d
  have hcL:algebraMap R L d*algebraMap B L c=1:=by
    rw [IsScalarTower.algebraMap_apply R B L,←map_mul,hc,map_one]
  apply top_unique
  intro z _
  obtain ⟨⟨a,t,ht⟩,hz⟩:=IsLocalization.surj (Submonoid.powers (algebraMap R A d)) z
  obtain ⟨n,rfl⟩:=ht
  have hz':z*(algebraMap R L d)^n=algebraMap A L a:=by
    simpa only [map_pow,←IsScalarTower.algebraMap_apply R A L] using hz
  have he:z=algebraMap A L a*(algebraMap B L c)^n:=by
    rw [←hz',mul_assoc,←mul_pow,hcL,one_pow,mul_one]
  rw [he]
  exact T.mul_mem (hA a) (T.pow_mem (T.algebraMap_mem c) n)
end LocalizedPrimitiveGeneration318
