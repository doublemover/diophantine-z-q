module
public import VaryingBoundedFamilyComponents318
public import VaryingBoundedFreeIdealMap318
public section
noncomputable section
namespace VaryingBoundedQuotientRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingBoundedDegreeFamily318
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S]
variable (n d : ℕ) (h : d ≤ n)
variable (I : VaryingFreeIdealClassifyingMap318.IdealData R A (Index.{u} d) S)
@[expose] def familyMap : VaryingFreeIdealFamilyRecovery318.family R A (Index.{u} d) S I ⟶ family R A n :=
  VaryingFreeIdealFamilyRecovery318.map R A (Index.{u} d) S I ≫
    VaryingBoundedFamilyComponents318.familyInclusion R A n d h
/-- Original degree-d free quotients are recovered from the actual bounded
family; d is any degree at most n, including zero. -/
lemma cartesian : IsPullback (familyMap R A S n d h I)
    (VaryingFreeIdealFamilyRecovery318.projection R A (Index.{u} d) S I)
    (projection R A n) (VaryingBoundedFreeIdealMap318.classify R A S n d h I) :=
  (VaryingFreeIdealFamilyRecovery318.cartesian R A (Index.{u} d) S I).paste_horiz
    (VaryingBoundedFamilyComponents318.cartesian R A n d h)
@[expose] def comparison : VaryingFreeIdealFamilyRecovery318.family R A (Index.{u} d) S I ≅
    pullback (projection R A n) (VaryingBoundedFreeIdealMap318.classify R A S n d h I) :=
  (cartesian R A S n d h I).isoPullback
/-- For fixed degree d, the bounded classifying map remains injective.
No disjointness of degree labels on empty test schemes is assumed. -/
lemma classify_injective : Function.Injective (VaryingBoundedFreeIdealMap318.classify R A S n d h) := by
  intro I J hIJ
  apply VaryingGlobalClassifierInjective318.classify_injective R A (Index.{u} d) S
  exact (cancel_mono (inclusion R A n d h)).mp hIJ
end VaryingBoundedQuotientRecovery318
