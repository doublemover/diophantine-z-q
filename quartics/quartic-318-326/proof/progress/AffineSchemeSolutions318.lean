module
public import AffineSchemeBaseChange318
public section
noncomputable section
namespace AffineSchemeSolutions318
open CategoryTheory AlgebraicGeometry ShortAffineJacobian318 AffineEquationFunctor318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R K:Type u} [CommRing R] [CommRing K] [Algebra R K]

/-- Genuine base-preserving Spec-valued points of the actual affine Scheme. -/
@[expose] def SchemePoints (A B:R) :=
  {f : Spec (CommRingCat.of K) ⟶ ShortAffineScheme318.scheme A B //
    f ≫ ShortAffineScheme318.structureMap A B =
      Spec.map (CommRingCat.ofHom (algebraMap R K))}

/-- Actual affine Scheme morphisms are equivalent to literal coordinate solutions. -/
@[expose] def schemeSolutionEquiv (A B:R) : SchemePoints (K:=K) A B ≃ Solutions (S:=K) A B :=
  Spec.homEquivAlgHom.trans (solutionEquiv A B)

/-- Exact coordinate morphism of a given literal solution. -/
theorem schemeSolutionEquiv_symm (A B:R) (p:Solutions (S:=K) A B) :
    ((schemeSolutionEquiv A B).symm p).val =
      Spec.map (CommRingCat.ofHom (toHom A B p).toRingHom) := rfl

end AffineSchemeSolutions318
