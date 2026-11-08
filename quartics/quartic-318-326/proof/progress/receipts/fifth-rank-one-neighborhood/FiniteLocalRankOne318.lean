module
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Free
public section
noncomputable section
namespace FiniteLocalRankOne318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable (A:Type u) (B:Type v) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [IsLocalRing A]
include A in
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
variable (L:Type w) [AddCommGroup L] [Module B L] [Module.Finite B L] [Module.Flat B L]
  (rk:∀q:PrimeSpectrum B,Module.rankAtStalk L q=1)
include A rk in
/-- A rank-one basis on the entire finite algebra over the local base,
from genuine finite-flat rank-one module hypotheses. -/
lemma exists_basis:Nonempty (Module.Basis (Fin 1) B L):=by
  letI:=finite_maximal A B
  apply Module.nonempty_basis_of_flat_of_finrank_eq B L 1
  intro q
  letI:Field (B⧸q.asIdeal):=Ideal.Quotient.field q.asIdeal
  let p:PrimeSpectrum (B⧸q.asIdeal):=⟨⊥,inferInstance⟩
  have h:=Module.rankAtStalk_baseChange (R:=B) (M:=L) (S:=B⧸q.asIdeal) p
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact h.trans (rk _)
end FiniteLocalRankOne318
