module
public import CocycleModule318
public section
noncomputable section
namespace CocycleEqualityTransport318
open AlgebraicGeometry CategoryTheory
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    {c d:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U}
/-- Literal equality transport of the original cocycle module. -/
@[expose] def iso (h:c=d):CocycleModule318.object U c≅CocycleModule318.object U d:=
  eqToIso (congrArg (CocycleModule318.object U) h)
lemma coefficient (h:c=d) (i:ι):(iso U h).hom≫CocycleModule318.coefficient U d i=
    CocycleModule318.coefficient U c i:=by
  subst d
  simp [iso]
/-- Retain an original source and its original coefficient family while
transporting the target along a proved cocycle equality. -/
@[expose] def changeTarget {M:X.Modules} (e:M≅CocycleModule318.object U c) (h:c=d):
    M≅CocycleModule318.object U d:=e≪≫iso U h
lemma changeTarget_coefficient {M:X.Modules} (e:M≅CocycleModule318.object U c)
    (h:c=d) (i:ι):(changeTarget U e h).hom≫CocycleModule318.coefficient U d i=
      e.hom≫CocycleModule318.coefficient U c i:=by
  rw [changeTarget,Iso.trans_hom,Category.assoc,coefficient]
end CocycleEqualityTransport318
