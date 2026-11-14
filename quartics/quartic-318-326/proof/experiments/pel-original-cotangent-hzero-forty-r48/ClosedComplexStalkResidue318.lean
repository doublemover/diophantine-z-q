module
public import CanonicalComplexStalkScalars318
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace ClosedComplexStalkResidue318
open AlgebraicGeometry CategoryTheory
open CanonicalComplexStalkScalars318
variable {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
/-- The SAME structural complex scalars, followed by the actual local
ring residue map. -/
@[expose] def residueBase (x : X) : ℂ →+* X.residueField x :=
  (X.residue x).hom.comp (stalkBase f x)
lemma base_residue_spec (y : Spec (CommRingCat.of ℂ)) :
    Spec.map (Scheme.Spec.residueFieldIsoOfField y).inv =
      (Spec (CommRingCat.of ℂ)).fromSpecResidueField y := by
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (Spec (CommRingCat.of ℂ)).Γevaluation y) = _
  simp only [Scheme.Γevaluation,Scheme.evaluation,Scheme.fromSpecResidueField,
    Scheme.Spec.fromSpecStalk_eq,Spec.map_comp,Category.assoc]
/-- Naturality proves that this precise residue scalar map is the
actual structure morphism of the residue-field point. -/
lemma residueBase_spec (x : X) :
    Spec.map (CommRingCat.ofHom (residueBase f x)) = X.fromSpecResidueField x ≫ f := by
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop ≫
    X.Γevaluation x) = _
  rw [←Scheme.Hom.residueFieldIsoOfField_inv_residueFieldMap,Spec.map_comp,
    base_residue_spec]
  exact f.SpecMap_residueFieldMap_fromSpecResidueField x
/-- At an actual closed point of a finite-type complex scheme, the
actual structural residue map is bijective, not an arbitrary abstract
field identification that might twist the complex scalars. -/
theorem residueBase_bijective [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    Function.Bijective (residueBase f x) := by
  have he : CommRingCat.ofHom (residueBase f x) = (residueFieldIsoBase f x hx).inv := by
    apply Spec.map_injective
    exact (residueBase_spec f x).trans (SpecMap_residueFieldIsoBase_inv f x hx).symm
  haveI : IsIso (CommRingCat.ofHom (residueBase f x)) := by rw [he]; infer_instance
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (residueBase f x))
theorem algebraMap_bijective [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := stalkAlgebra f x
    Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  change Function.Bijective (residueBase f x)
  exact residueBase_bijective f x hx
end ClosedComplexStalkResidue318
