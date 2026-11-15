module
public import ActualTwoDescentOriginalOverlapPoleIdentity318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapSquareSections318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentOriginalPuncturedCharts318
open ActualTwoDescentOriginalOverlapQuotientMaps318 ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentOriginalGlobalInfinityPoleUnit318 ActualTwoDescentOriginalInverseInfinityTransition318
open ActualTwoDescentOriginalRootNativeSquareCharts318 ActualTwoDescentOriginalOverlapPoleIdentity318
universe u
variable {K : Type u} [Field K] [CharZero K]

def affineRootSection (n : K) (i : Fin 3) : Γ(affineScheme n,⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (AffineChart n))).inv (rootNumerator n i)
def rootSection (n : K) (i : Fin 3) : Γ(overlapScheme n,⊤) :=
  (intoAffine n).appTop (affineRootSection n i)
def infinityCoefficient (n : K) (i : Fin 3) : Γ(overlapScheme n,⊤) :=
  (intoInfinity n).appTop (infinitySquareCoefficient n i)

def rootSectionUnit (n : K) (i : Fin 3) : Γ(overlapScheme n,⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv.hom.toMonoidHom (overlapRootUnit n i)

lemma rootSection_value (n : K) (i : Fin 3) : rootSection n i=
    (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv (overlapRoot n i) := by
  unfold rootSection affineRootSection
  rw [actual_into_affine]
  exact (congrArg (fun f => f (rootNumerator n i))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (affineToInfinity n)))).symm
lemma infinityCoefficient_value (n : K) (i : Fin 3) : infinityCoefficient n i=
    (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv
      (infinityOpenMap n (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n)) :=
  (congrArg (fun f => f (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (infinityOpenMap n)))).symm
lemma rootSectionUnit_value (n : K) (i : Fin 3) :
    (rootSectionUnit n i : Γ(overlapScheme n,⊤))=rootSection n i := by
  change (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv (overlapRootUnit n i)=_
  rw [actual_overlap_root_unit,rootSection_value]

/-- Equality of actual original regular sections on the COMPLETE
common chart. No injection into the function field is used. -/
lemma actual_section_square (n : K) (i : Fin 3) :
    rootSection n i*infinityCoefficient n i=inverseUSection n^2 := by
  rw [rootSection_value,infinityCoefficient_value]
  change _=((Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv (overlapInverseU n))^2
  rw [←map_mul,actual_overlap_square_coefficient,map_pow]

lemma actual_inverse_section_square (n : K) (i : Fin 3) :
    (inverseUSection n)^2*((rootSectionUnit n i)⁻¹ : Γ(overlapScheme n,⊤)ˣ)=infinityCoefficient n i := by
  rw [←actual_section_square,←rootSectionUnit_value]
  calc
    _=infinityCoefficient n i*((rootSectionUnit n i : Γ(overlapScheme n,⊤))*
      ((rootSectionUnit n i)⁻¹ : Γ(overlapScheme n,⊤)ˣ)) := by ring
    _=_ := by rw [Units.mul_inv,mul_one]
end ActualTwoDescentOriginalOverlapSquareSections318
