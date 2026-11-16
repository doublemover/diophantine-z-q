module
public import OriginalRegularClosedCharts318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace RegularAffineChartFlat318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A : CommRingCat.{u}) [Algebra R A] {Z X : Scheme.{u}}
  (p : Z ⟶ X) (a : X ⟶ Spec R) (j : Spec A ⟶ X)
  [IsOpenImmersion j] (hj : j ≫ a=Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (c : A) (z : Spec (CommRingCat.of (A ⧸ Ideal.span ({c} : Set A))) ⟶ Z)
  (H : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({c} : Set A))))) z j p)
  [hflat : Flat (p ≫ a)]
include hj H hflat in
/-- Flatness of the WHOLE family gives flatness of its actual principal
chart quotient over the original coefficient ring. No target-chart
flatness or flatness of a future coefficient change is assumed. -/
lemma flat : Module.Flat R (A ⧸ Ideal.span ({c} : Set A)) := by
  letI : IsOpenImmersion z := MorphismProperty.of_isPullback H inferInstance
  have hz : Flat (z ≫ (p ≫ a)) := inferInstance
  have he : z ≫ (p ≫ a)=Spec.map (CommRingCat.ofHom
      (algebraMap R (A ⧸ Ideal.span ({c} : Set A)))) := by
    rw [← Category.assoc,← H.w,Category.assoc,hj,← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    rfl
  rw [he] at hz
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hz)
end RegularAffineChartFlat318
