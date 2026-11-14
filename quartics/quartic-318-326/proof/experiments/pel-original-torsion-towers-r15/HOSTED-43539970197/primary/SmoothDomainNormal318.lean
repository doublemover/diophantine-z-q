module
public import EtaleDomainNormal318
public import NormalitySpanDescent318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace SmoothDomainNormal318
open Algebra
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable (K B:Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.Smooth K B]
include K

lemma local_normal (m:PrimeSpectrum B) :
    ∃f∉m.asIdeal,IsIntegrallyClosed (Localization.Away f) := by
  obtain ⟨f,hfm,n,alg,tower,et⟩:=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R:=K) (p:=m.asIdeal)
  letI:Algebra (MvPolynomial (Fin n) K) (Localization.Away f):=alg
  letI:IsScalarTower K (MvPolynomial (Fin n) K) (Localization.Away f):=tower
  letI:Algebra.IsStandardEtale (MvPolynomial (Fin n) K) (Localization.Away f):=et
  have hf:f≠0:=by intro h;apply hfm;rw [h];exact Ideal.zero_mem _
  letI:IsDomain (Localization.Away f):=IsLocalization.Away.isDomain _ hf
  exact ⟨f,hfm,EtaleDomainNormal318.integrallyClosed
    (R:=MvPolynomial (Fin n) K) (K:=FractionRing (MvPolynomial (Fin n) K))⟩

/-- A smooth domain over a field is normal, proved through actual principal
standard-etale neighborhoods over polynomial rings. -/
theorem integrallyClosed : IsIntegrallyClosed B := by
  choose f hfm hn using local_normal K B
  apply NormalitySpanDescent318.of_principal_cover f _ hn
  by_contra h
  obtain ⟨m,hm,hle⟩:=Ideal.exists_le_maximal (Ideal.span (Set.range f)) h
  let p:PrimeSpectrum B:=⟨m,hm.isPrime⟩
  exact hfm p (hle (Ideal.subset_span (show f p∈Set.range f from ⟨p,rfl⟩)))
end SmoothDomainNormal318
