module
public import VaryingFreeIdealFamilyRecovery318
public section
noncomputable section
namespace VaryingParameterPoint318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- Actual R-valued points of the glued parameter scheme, with the original
coefficient structure retained. No quotient-frame witness is part of a point. -/
abbrev Point := {f : Spec (CommRingCat.of S) ⟶ VaryingWordChartGluing318.scheme R A ι //
  f ≫ VaryingWordParameterStructure318.structureMap R A ι=VaryingSourceCoefficientPullback318.base R S}
@[expose] def ofIdeal (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S) : Point R A ι S :=
  ⟨VaryingFreeIdealClassifyingMap318.classify R A ι S I,VaryingFreeIdealClassifyingMap318.over_base R A ι S I⟩
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
@[expose] def map (x : Point R A ι S) : Point R A ι T :=
  ⟨VaryingSourceCoefficientPullback318.coefficientChange R S T f ≫ x.val,by
    rw [Category.assoc,x.property,VaryingSourceCoefficientPullback318.coefficient_base]⟩
lemma map_ofIdeal (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S) :
    map R A ι S T f (ofIdeal R A ι S I)=
    ofIdeal R A ι T (VaryingFreeIdealClassifyingMap318.mapIdeal R A ι S T f I) := by
  apply Subtype.ext
  exact VaryingFreeIdealClassifyingMap318.natural R A ι S T f I
end VaryingParameterPoint318
