module
public import VaryingLocalIdealTestAgreement318
public import AffineCoefficientOverlapTests318
public section
noncomputable section
namespace VaryingLocalFreeIdealGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingLocalFreeIdealCover318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : Ideal (S ⊗[R] A)) (C : Data R A ι S I)
local notation "U" => AffineCoefficientCover318.cover R S C.coefficients
lemma compatible (i j : C.coefficients.Index) :
    pullback.fst (U.f i) (U.f j) ≫ localMap R A ι S I C i=
    pullback.snd (U.f i) (U.f j) ≫ localMap R A ι S I C j := by
  let V := (pullback (U.f i) (U.f j)).affineOpenCover
  apply Scheme.Cover.hom_ext V.openCover _ _
  intro k
  have h := VaryingLocalIdealTestAgreement318.agreement R A ι S I C i j
    (AffineCoefficientOverlapTests318.ring R S C.coefficients i j k)
    (AffineCoefficientOverlapTests318.leftHom R S C.coefficients i j k)
    (AffineCoefficientOverlapTests318.rightHom R S C.coefficients i j k)
    (AffineCoefficientOverlapTests318.hom_comp R S C.coefficients i j k)
  rw [AffineCoefficientOverlapTests318.left_spec,AffineCoefficientOverlapTests318.right_spec] at h
  simpa only [AffineCoefficientOverlapTests318.left,AffineCoefficientOverlapTests318.right,
    Category.assoc] using h
/-- Actual gluing of classifying maps for a locally free full quotient
ideal, using its whole genuine coefficient cover. No global basis exists
in this input, and no abstract map with a chosen recovery property is assumed. -/
@[expose] def classify : Spec (CommRingCat.of S) ⟶ VaryingWordChartGluing318.scheme R A ι :=
  U.glueMorphisms (localMap R A ι S I C) (compatible R A ι S I C)
@[reassoc] lemma into_classify (i : C.coefficients.Index) :
    U.f i ≫ classify R A ι S I C=localMap R A ι S I C i :=
  U.ι_glueMorphisms (localMap R A ι S I C) (compatible R A ι S I C) i
@[reassoc] lemma over_base : classify R A ι S I C ≫
    VaryingWordParameterStructure318.structureMap R A ι=VaryingSourceCoefficientPullback318.base R S := by
  apply Scheme.Cover.hom_ext U _ _
  intro i
  rw [← Category.assoc,into_classify,AffineCoefficientCover318.over_base]
  exact VaryingFreeIdealClassifyingMap318.over_base R A ι (C.coefficients.ring i) (localIdeal R A ι S I C i)
@[expose] def point : VaryingParameterPoint318.Point R A ι S :=
  ⟨classify R A ι S I C,over_base R A ι S I C⟩
/-- The local restrictions characterize the actual glued map uniquely. -/
lemma unique (y : VaryingParameterPoint318.Point R A ι S)
    (hy : ∀ i,U.f i ≫ y.val=localMap R A ι S I C i) : y=point R A ι S I C := by
  apply Subtype.ext
  apply Scheme.Cover.hom_ext U _ _
  intro i
  exact (hy i).trans (into_classify R A ι S I C i).symm
end VaryingLocalFreeIdealGluing318
