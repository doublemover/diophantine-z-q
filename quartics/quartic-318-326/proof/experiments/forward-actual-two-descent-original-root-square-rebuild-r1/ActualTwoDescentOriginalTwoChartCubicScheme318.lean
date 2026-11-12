module
public import ActualTwoDescentOriginalGlobalInfinityPoleUnit318
public import WeierstrassGluing318
public section
noncomputable section
namespace ActualTwoDescentOriginalTwoChartCubicScheme318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapQuotientMaps318
open ActualTwoDescentOriginalOverlapLocalizationMaps318 ActualTwoDescentOriginalOverlapEquivalence318
variable {K : Type*} [Field K] [CharZero K]

abbrev affineScheme (n : K) : Scheme := Spec (CommRingCat.of (AffineChart n))
abbrev infinityScheme (n : K) : Scheme := Spec (CommRingCat.of (InfinityChart n))
abbrev overlapScheme (n : K) : Scheme := Spec (CommRingCat.of (InfinityPuncture n))
def intoInfinity (n : K) : overlapScheme n ⟶ infinityScheme n :=
  Spec.map (CommRingCat.ofHom (infinityOpenMap n))
instance intoInfinity_open (n : K) : IsOpenImmersion (intoInfinity n) :=
  IsOpenImmersion.of_isLocalization (chartV n)
def intoAffine (n : K) : overlapScheme n ⟶ affineScheme n :=
  Spec.map (originalOverlapEquiv n).toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (affineOpenMap n))
instance intoAffine_open (n : K) : IsOpenImmersion (intoAffine n) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineOpenMap n))) :=
    IsOpenImmersion.of_isLocalization (affineY n)
  unfold intoAffine
  infer_instance

lemma actual_into_affine (n : K) :
    intoAffine n=Spec.map (CommRingCat.ofHom (affineToInfinity n)) := by
  unfold intoAffine
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact actual_affine_overlap_base n a

def affineStructure (n : K) : affineScheme n ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (affineCoefficient n))
def infinityStructure (n : K) : infinityScheme n ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (chartCoefficient n))
lemma actual_overlap_over_base (n : K) :
    intoAffine n ≫ affineStructure n=intoInfinity n ≫ infinityStructure n := by
  rw [actual_into_affine]
  unfold affineStructure intoInfinity infinityStructure
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact actual_affine_to_infinity_coefficient n a

/-- The actual scheme glued from the two original cubic coordinate
rings by their explicit reciprocal substitution. No abstract model or
merely topological pushout replaces the native scheme pushout. -/
abbrev originalCubicScheme (n : K) : Scheme := pushout (intoAffine n) (intoInfinity n)
def affineChart (n : K) : affineScheme n ⟶ originalCubicScheme n := pushout.inl _ _
def infinityChart (n : K) : infinityScheme n ⟶ originalCubicScheme n := pushout.inr _ _
instance affineChart_open (n : K) : IsOpenImmersion (affineChart n) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoAffine n) (intoInfinity n)) WalkingSpan.left))
instance infinityChart_open (n : K) : IsOpenImmersion (infinityChart n) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoAffine n) (intoInfinity n)) WalkingSpan.right))
def structureMap (n : K) : originalCubicScheme n ⟶ Spec (CommRingCat.of K) :=
  pushout.desc (affineStructure n) (infinityStructure n) (actual_overlap_over_base n)
@[simp] lemma actual_affine_chart_structure (n : K) :
    affineChart n ≫ structureMap n=affineStructure n := pushout.inl_desc ..
@[simp] lemma actual_infinity_chart_structure (n : K) :
    infinityChart n ≫ structureMap n=infinityStructure n := pushout.inr_desc ..
end ActualTwoDescentOriginalTwoChartCubicScheme318
