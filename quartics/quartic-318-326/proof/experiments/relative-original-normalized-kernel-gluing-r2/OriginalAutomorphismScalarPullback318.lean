module
public import ContactOriginalNestedFunctionConstants318
public import OriginalModuleScalarPullback318
public section
noncomputable section
namespace OriginalAutomorphismScalarPullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (L : Line Y)
/-- The CURRENT full automorphism-unit classifier commutes with actual
module pullback, using the old proved module-scalar pullback equation. -/
lemma value (e : L.object ≅ L.object) :
    OriginalLineAutomorphismUnits318.value (LineSheafPullback318.line f L)
      ((Scheme.Modules.pullback f).mapIso e)=
    Units.map f.appTop.hom.toMonoidHom (OriginalLineAutomorphismUnits318.value L e) := by
  apply Units.ext
  change OriginalLineEndScalars318.scalar (LineSheafPullback318.line f L)
    ((Scheme.Modules.pullback f).map e.hom)=f.appTop (OriginalLineEndScalars318.scalar L e.hom)
  rw [OriginalLineEndScalars318.map_eq L e.hom,
    OriginalModuleScalarPullback318.pullback_scalar,OriginalLineEndScalars318.scalar_map]
variable (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g=k) (M : Line Z)
/-- The ACTUAL native path associator does not change the pulled scalar.
This is the precise coefficient action used by the original classifier. -/
lemma path_value
    (e : (LineSheafPullback318.line g M).object ≅ (LineSheafPullback318.line g M).object) :
    OriginalLineAutomorphismUnits318.value (LineSheafPullback318.line k M)
      (OriginalPulledDifferencePath318.pullIso f g k h M M e)=
    Units.map f.appTop.hom.toMonoidHom
      (OriginalLineAutomorphismUnits318.value (LineSheafPullback318.line g M) e) := by
  unfold OriginalPulledDifferencePath318.pullIso
  rw [OriginalLineIsomScalarCompatibility318.automorphism_conjugation]
  exact value f (LineSheafPullback318.line g M) e
end OriginalAutomorphismScalarPullback318
