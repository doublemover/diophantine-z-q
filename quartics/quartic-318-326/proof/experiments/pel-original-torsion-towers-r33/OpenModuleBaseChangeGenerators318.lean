module
public import OpenModuleBaseChangeUnit318
public import OpenScalarSheafNaturality318
public import ChartGeneratedImageSheaf318
public section
noncomputable section
namespace OpenModuleBaseChangeGenerators318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GlobalScalarSheafEndomorphism318 IntegralOpenUnitMonomorphism318
open OpenModuleCartesianBaseChange318 OpenModuleBaseChangeUnit318 OpenScalarSheafNaturality318
variable {W U V X : Scheme} (right : W ⟶ V) (left : W ⟶ U)
  (k : V ⟶ X) (j : U ⟶ X)
  [IsOpenImmersion right] [IsOpenImmersion left] [IsOpenImmersion k] [IsOpenImmersion j]
  (H : IsPullback right left k j)

/-- Full scalar compatibility of the unit-specialized base-change iso. -/
theorem unitIso_scalar (r : Γ(U,⊤)) :
    (Scheme.Modules.restrictFunctor k).map
      ((Scheme.Modules.pushforward j).map (endomorphism U r))≫(unitIso right left k j H).hom=
    (unitIso right left k j H).hom≫
      (Scheme.Modules.pushforward right).map (endomorphism W (left.appTop r)) := by
  have hn := (baseChange right left k j H).hom.naturality (endomorphism U r)
  change (Scheme.Modules.restrictFunctor k).map
      ((Scheme.Modules.pushforward j).map (endomorphism U r))≫
      (objectIso right left k j H (SheafOfModules.unit U.ringCatSheaf)).hom=
    (objectIso right left k j H (SheafOfModules.unit U.ringCatSheaf)).hom≫
      (Scheme.Modules.pushforward right).map ((Scheme.Modules.restrictFunctor left).map
        (endomorphism U r)) at hn
  rw [unitIso,Iso.trans_hom,Functor.mapIso_hom,←Category.assoc,hn,
    Category.assoc,←Functor.map_comp,restriction_square,Functor.map_comp]
  simp only [Category.assoc]

/-- The adjunction-defined actual chart generator is the genuine unit
map followed by direct image of literal scalar multiplication. -/
theorem generator_factor {ι : Type} (r : ι → Γ(U,⊤)) (i : ι) :
    ChartGeneratedImageSheaf318.generator j r i=
      unitMap j≫(Scheme.Modules.pushforward j).map (endomorphism U (r i)) :=
  (Scheme.Modules.restrictAdjunction j).homEquiv_naturality_right
    (Scheme.Modules.restrictUnitIso j).hom (endomorphism U (r i))

/-- Exact generator formula on a whole Cartesian chart intersection.
It is a full module-sheaf identity, with the coefficient the ACTUAL
pullback of the original regular ratio; no sections-only factorization. -/
theorem generator_square {ι : Type} (r : ι → Γ(U,⊤)) (i : ι) :
    (Scheme.Modules.restrictUnitIso k).inv≫
      (Scheme.Modules.restrictFunctor k).map (ChartGeneratedImageSheaf318.generator j r i)≫
        (unitIso right left k j H).hom=
    unitMap right≫(Scheme.Modules.pushforward right).map (endomorphism W (left.appTop (r i))) := by
  rw [generator_factor,Functor.map_comp,Category.assoc,unitIso_scalar,
    ←Category.assoc,unit_square]
end OpenModuleBaseChangeGenerators318
