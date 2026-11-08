module
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Free
public section
noncomputable section
namespace FiniteLocalInvertible318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable (A:Type u) (B:Type v) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [IsLocalRing A]
/-- The entire finite algebra over a local base is semilocal, not merely
one chosen localization at a source prime. -/
lemma finite_maximal:Finite (MaximalSpectrum B):=by
  have hf:((IsLocalRing.maximalIdeal A).primesOver B).Finite:=
    Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal A)
  let e:MaximalSpectrum B→(IsLocalRing.maximalIdeal A).primesOver B:=fun q=>
    ⟨q.asIdeal,q.isMaximal.isPrime,⟨(IsLocalRing.eq_maximalIdeal
      (inferInstanceAs (q.asIdeal.under A).IsMaximal)).symm⟩⟩
  letI:Finite ((IsLocalRing.maximalIdeal A).primesOver B):=hf.to_subtype
  exact Finite.of_injective e (fun q r h=>MaximalSpectrum.ext (congrArg Subtype.val h))
variable (L:Type w) [AddCommGroup L] [Module B L] [Module.Invertible B L]
/-- Actual linear equivalence for any invertible module on the entire finite
algebra above a local base; the source algebra need not itself be local. -/
lemma exists_equiv:Nonempty (L≃ₗ[B]B):=by
  letI:=finite_maximal A B
  letI:Subsingleton (CommRing.Pic B):=inferInstance
  letI:Module.Free B L:=inferInstance
  exact Module.Invertible.free_iff_linearEquiv.mp inferInstance
end FiniteLocalInvertible318
