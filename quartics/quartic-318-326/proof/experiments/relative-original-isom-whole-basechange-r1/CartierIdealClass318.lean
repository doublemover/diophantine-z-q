module
public import InvertibleIdealUniqueness318
public import ActualCartierIdealLine318
public section
noncomputable section
namespace CartierIdealClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (h : OriginalRegularClosedCharts318.Property p)

/-- The actual ideal-line class of the original Cartier embedding. It is
canonical despite choosing quotient charts to exhibit invertibility. -/
@[expose] def value : Class X := classOf (ActualCartierIdealLine318.line p h)
lemma chart_independent (h' : OriginalRegularClosedCharts318.Property p) :
    value p h=value p h' := by
  apply LineSheafClass318.classOf_eq
  exact eqToIso ((ActualCartierIdealLine318.object_eq p h).trans
    (ActualCartierIdealLine318.object_eq p h').symm)

/-- A mono line presentation defining the same literal affine ideals has
exactly the original ideal-line class. This is an actual sheaf isomorphism
with prescribed inclusion, not equality of fiber dimensions or supports. -/
lemma presentation (L : Line X) (f : L.object ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono f]
    (he : ∀ V : X.affineOpens,LinearMap.range (f.val.app (op V.1)).hom=p.ker.ideal V) :
    classOf L=value p h := by
  apply LineSheafClass318.classOf_eq
  exact InvertibleIdealUniqueness318.iso p L f he ≪≫
    eqToIso (ActualCartierIdealLine318.object_eq p h).symm
end CartierIdealClass318
