module
public import ScalarExtensionOriginalSpan318
public import OriginalTensorChartRestriction318
public section
noncomputable section
namespace OriginalAffineOverlapSpan318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
  (L : Line (Spec B)) {X : Scheme.{u}} (p : X ⟶ Spec A) (j : X ⟶ Spec B)
  (i : Spec (ring R A B) ≅ X)
  (hbase : i.hom ≫ p = Spec.map (leftMap R A B))
  (hchart : i.hom ≫ j = Spec.map (rightMap R A B))
  (M : X.Modules) (e : (Scheme.Modules.pullback j).obj L.object ≅ M)

/-- The restriction of an ORIGINAL affine line chart to the actual full
geometric tensor overlap, with the unchanged pushforward section carrier. -/
def restriction (m : OriginalLineAffineModel318.sections B L) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward p).obj M) :=
  (OriginalTensorChartRestriction318.chartRecovery R A B L p j i hbase hchart M e).hom
    ((TildePullback318.globalNatIso (rightMap R A B)).hom.app _
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (rightMap R A B))).unit.app L.object) m))

/-- The actual geometric restriction image spans the entire original
pushforward overlap module. The span is proved from the OLD tensor
comparison and its OLD pullback-unit square; it is not a new input. No
base-domain, reducedness, freeness or finite-rank premise is needed. -/
theorem span_restriction :
    Submodule.span A (Set.range (restriction R A B L p j i hbase hchart M e)) = ⊤ := by
  exact ScalarExtensionOriginalSpan318.original_span (algebraMap R A)
    ((ModuleCat.restrictScalars (algebraMap R B)).obj
      (OriginalLineAffineModel318.sections B L))
    (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward p).obj M))
    (AffineTensorLinePushforward318.sectionsIso R A B p j i hbase hchart L M e)
    (restriction R A B L p j i hbase hchart M e)
    (OriginalTensorChartRestriction318.overlap_unit R A B L p j i hbase hchart M e)
end OriginalAffineOverlapSpan318
