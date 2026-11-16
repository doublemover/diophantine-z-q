module
public import VaryingWholeQuotientTensor318
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public section
noncomputable section
namespace VaryingWholeQuotientRank318
open scoped TensorProduct
universe u
variable (R A S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (I : Ideal (S ⊗[R] A)) [Module.Flat S ((S ⊗[R] A) ⧸ I)]
  [Module.Finite S ((S ⊗[R] A) ⧸ I)]
/-- Stalk rank is preserved by arbitrary original coefficient base change,
using the full-ideal tensor equivalence, with no flatness hypothesis on T. -/
lemma degree_baseChange (p : PrimeSpectrum T) :
    Module.rankAtStalk ((T ⊗[R] A) ⧸ VaryingWholeQuotientTensor318.ideal R A S T I) p=
      Module.rankAtStalk ((S ⊗[R] A) ⧸ I) (p.comap (algebraMap S T)) := by
  have h := congrFun (Module.rankAtStalk_eq_of_equiv
    (VaryingWholeQuotientTensor318.equivalence R A S T I).toLinearEquiv) p
  exact h.symm.trans (Module.rankAtStalk_baseChange (M := (S ⊗[R] A) ⧸ I) p)
end VaryingWholeQuotientRank318
