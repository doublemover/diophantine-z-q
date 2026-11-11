module
public import GlobalScalarSheafEndomorphism318
public import IntegralOpenUnitMonomorphism318
public section
noncomputable section
namespace OpenScalarSheafNaturality318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalScalarSheafEndomorphism318 IntegralOpenUnitMonomorphism318
variable {U X : Scheme} (f : U ⟶ X)

/-- Full structure-sheaf naturality for the restrictions of a genuine
global function, on every open of the target. -/
lemma global_app (r : Γ(X,⊤)) (O : X.Opens) :
    f.app O (X.presheaf.map (homOfLE (show O≤⊤ from le_top)).op r)=
      U.presheaf.map (homOfLE (show f ⁻¹ᵁ O≤⊤ from le_top)).op (f.appTop r) :=
  congrArg (fun h => h r) (f.naturality (homOfLE (show O≤⊤ from le_top)).op)

variable [IsOpenImmersion f]

/-- The actual open-chart scalar identification carries a restricted
global function to the literal pullback global function. -/
lemma global_appIso (r : Γ(X,⊤)) (O : U.Opens) :
    (f.appIso O).hom (X.presheaf.map (homOfLE (show f ''ᵁ O≤⊤ from le_top)).op r)=
      U.presheaf.map (homOfLE (show O≤⊤ from le_top)).op (f.appTop r) := by
  have h : X.presheaf.map (homOfLE (show f ''ᵁ O≤⊤ from le_top)).op≫
      (f.appIso O).hom=f.appTop≫U.presheaf.map (homOfLE (show O≤⊤ from le_top)).op := by
    rw [Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE,Scheme.Hom.appLE] <;> rfl
  exact congrArg (fun h => h r) h

/-- Restriction of actual scalar multiplication commutes with the
produced structure-module frame. -/
theorem restriction_square (r : Γ(X,⊤)) :
    (Scheme.Modules.restrictFunctor f).map (endomorphism X r)≫
      (Scheme.Modules.restrictUnitIso f).hom=
    (Scheme.Modules.restrictUnitIso f).hom≫endomorphism U (f.appTop r) := by
  apply Scheme.Modules.hom_ext
  intro O
  ext a
  change (f.appIso O).hom ((endomorphism X r).app (f ''ᵁ O) a)=
    (endomorphism U (f.appTop r)).app O ((f.appIso O).hom a)
  rw [endomorphism_apply,endomorphism_apply,map_mul,global_appIso]

/-- Conjugation form, useful for gluing actual scalar transition maps. -/
theorem restriction_conjugate (r : Γ(X,⊤)) :
    (Scheme.Modules.restrictUnitIso f).inv≫
      (Scheme.Modules.restrictFunctor f).map (endomorphism X r)≫
        (Scheme.Modules.restrictUnitIso f).hom=endomorphism U (f.appTop r) := by
  rw [restriction_square,Iso.inv_hom_id_assoc]

/-- Actual unit-map/scalar naturality on all opens, not just global
sections. This is the coefficient square used by the image-sheaf
presentation on genuine chart intersections. -/
theorem unit_scalar_square (r : Γ(X,⊤)) :
    endomorphism X r≫unitMap f=
      unitMap f≫(Scheme.Modules.pushforward f).map (endomorphism U (f.appTop r)) := by
  apply Scheme.Modules.hom_ext
  intro O
  ext a
  change (unitMap f).app O ((endomorphism X r).app O a)=
    (endomorphism U (f.appTop r)).app (f ⁻¹ᵁ O) ((unitMap f).app O a)
  rw [unitMap_app,unitMap_app,endomorphism_apply,endomorphism_apply,map_mul,global_app]
end OpenScalarSheafNaturality318
