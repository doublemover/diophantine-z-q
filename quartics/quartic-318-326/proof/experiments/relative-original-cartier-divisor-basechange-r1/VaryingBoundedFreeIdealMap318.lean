module
public import VaryingBoundedDegreeFamily318
public section
noncomputable section
namespace VaryingBoundedFreeIdealMap318
open AlgebraicGeometry CategoryTheory
open VaryingBoundedDegreeFamily318
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S]
variable (n d : ℕ) (hd : d ≤ n)
/-- Actual natural map of globally free degree-d original quotients into
the bounded-degree parameter. No universal inverse is assumed. -/
@[expose] def classify (I : VaryingFreeIdealClassifyingMap318.IdealData R A (Index.{u} d) S) :
    Spec (CommRingCat.of S) ⟶ parameter R A n :=
  VaryingFreeIdealClassifyingMap318.classify R A (Index.{u} d) S I ≫ inclusion R A n d hd
@[reassoc] lemma over_base (I : VaryingFreeIdealClassifyingMap318.IdealData R A (Index.{u} d) S) :
    classify R A S n d hd I ≫ structureMap R A n=VaryingSourceCoefficientPullback318.base R S := by
  rw [classify,Category.assoc,inclusion_structure,VaryingFreeIdealClassifyingMap318.over_base]
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
lemma natural (I : VaryingFreeIdealClassifyingMap318.IdealData R A (Index.{u} d) S) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ classify R A S n d hd I=
      classify R A T n d hd (VaryingFreeIdealClassifyingMap318.mapIdeal R A (Index.{u} d) S T f I) := by
  simpa only [classify,Category.assoc] using congrArg (fun q => q ≫ inclusion R A n d hd)
    (VaryingFreeIdealClassifyingMap318.natural R A (Index.{u} d) S T f I)
end VaryingBoundedFreeIdealMap318
