module
public import ActualCartierSheafFrame318
public import OriginalRegularClosedCharts318
public section
noncomputable section
namespace ActualCartierIdealLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineQuotientKernelSections318
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]

/-- The actual global zero-kernel module is an invertible sheaf whenever
its ORIGINAL quotient charts have nonzerodivisor equations. Local frames
are genuine sheaf isomorphisms, constructed on all affine subopens. -/
@[expose] def line (h : OriginalRegularClosedCharts318.Property p) : LineSheafClass318.Line X := by
  classical
  choose A j hj hx c z hs hc using h
  letI : ∀ x,IsOpenImmersion (j x) := hj
  refine { object := ActualClosedIdealModule318.object p
           Index := X
           opens := fun x => (chartOpen (A x) (j x)).1
           cover := ?_
           frame := fun x => ActualCartierSheafFrame318.frame p (A x) (j x) (c x)
             (z x) (hs x) (hc x) }
  intro x _
  apply (le_iSup (fun y => (chartOpen (A y) (j y)).1) x)
  obtain ⟨a,ha⟩ := hx x
  exact ⟨a,Set.mem_univ a,ha⟩

lemma object_eq (h : OriginalRegularClosedCharts318.Property p) :
    (line p h).object=ActualClosedIdealModule318.object p := rfl

/-- The inclusion still lands in the original structure sheaf and cuts
out exactly the original closed zero object; no new ideal is substituted. -/
@[expose] def inclusion (h : OriginalRegularClosedCharts318.Property p) :
    (line p h).object ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ActualClosedIdealModule318.inclusion p
end ActualCartierIdealLine318
