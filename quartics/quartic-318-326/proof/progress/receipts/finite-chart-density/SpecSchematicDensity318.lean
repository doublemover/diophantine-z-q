module
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public section
noncomputable section
namespace SpecSchematicDensity318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Injectivity of the actual ring map gives schematic density of its Spec
map, without requiring the rings to be reduced. -/
theorem spec_of_injective {R S:CommRingCat} (φ:R⟶S) (hφ:Function.Injective φ) :
    IsSchemeTheoreticallyDominant (Spec.map φ):=by
  have htop:Function.Injective (Spec.map φ).appTop:=by
    intro x y h
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1
    apply hφ
    have he:=congrArg (fun z=>(Scheme.ΓSpecIso S).hom z) h
    change ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso S).hom) x =
      ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso S).hom) y at he
    rw [Scheme.ΓSpecIso_naturality] at he
    exact he
  constructor
  exact Scheme.IdealSheafData.ext_of_isAffine (by
    simpa [(Spec.map φ).ker_apply ⟨⊤,isAffineOpen_top (Spec R)⟩,
      ←RingHom.injective_iff_ker_eq_bot] using htop)
end SpecSchematicDensity318
