module
public import AffineFaithfullyFlatChart318
public import AffineDescentCompositionComparison318
public import AffineBaseChangeNaturality318
public section
noncomputable section
namespace AffineOpenChartDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open AffineFaithfullyFlatChart318
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
  (U : Y.Opens) (hU : IsAffineOpen U)
local instance chartAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := algebra f U

/-- Original geometric descent data restricted to the actual affine chart.
Both laws are derived along the original Cartesian square. -/
@[expose] def datum (D : OriginalSchemeDescentData318.Datum f) :
    ActualAffineDescentData318.Datum Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  OriginalSchemeDescentData318.toAffine _ _
    (OriginalSchemeDescentBaseChange318.datum f (map f U) (source f U hU) (base U hU)
      (square f U hU) D)

@[expose] def mapDatum {D E : OriginalSchemeDescentData318.Datum f}
    (k : OriginalSchemeDescentBaseChangeMaps318.Hom D E) :
    ActualAffineDescentData318.Hom (datum f U hU D) (datum f U hU E) where
  sheafHom := (Scheme.Modules.pullback (source f U hU)).map k.sheafHom
  commutes := (OriginalSchemeDescentBaseChangeMaps318.map (map f U)
    (source f U hU) (base U hU) (square f U hU) k).commutes

variable [Flat f] [Surjective f]
local instance chartFaithfullyFlat : Module.FaithfullyFlat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  module_faithfullyFlat f U hU

abbrev line (D : OriginalSchemeDescentData318.Datum f) :=
  ActualAffineDescendedMaps318.line (datum f U hU D)
abbrev comparison (D : OriginalSchemeDescentData318.Datum f) :=
  ActualAffineDescendedMaps318.comparison (datum f U hU D)

lemma original_overlap (D : OriginalSchemeDescentData318.Datum f) :
    CanonicalSheafOverlap318.actual (line f U hU D).object (map f U) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (map f U))).map
        (comparison f U hU D).hom =
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (map f U))).map
      (comparison f U hU D).hom ≫ (datum f U hU D).overlap :=
  ActualAffineEffectiveComparison318.comparison_commutes _ _
    (datum f U hU D).line (datum f U hU D).overlap
    (datum f U hU D).diagonal (datum f U hU D).triple

/-- Every compatible original global covering map has a unique chart map
with its literal original pulled-back covering map. -/
theorem maps_effective {D E : OriginalSchemeDescentData318.Datum f}
    (k : OriginalSchemeDescentBaseChangeMaps318.Hom D E) :
    ∃! t : (line f U hU D).object ⟶ (line f U hU E).object,
      (Scheme.Modules.pullback (map f U)).map t ≫ (comparison f U hU E).hom =
        (comparison f U hU D).hom ≫ (Scheme.Modules.pullback (source f U hU)).map k.sheafHom :=
  ActualAffineDescendedMaps318.exists_unique_map (mapDatum f U hU k)

end AffineOpenChartDescent318
