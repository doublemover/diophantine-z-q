module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace AffineModuleBasisFrame318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R:CommRingCat.{u}} (M:(Spec R).Modules) [M.IsQuasicoherent]
/-- An actual basis of the original affine global-section module gives an
actual free-sheaf frame of the original quasicoherent module sheaf. -/
@[expose] def frame {ι:Type u} (b:Module.Basis ι R (moduleSpecΓFunctor.obj M)):
    SheafOfModules.free (R:=(Spec R).ringCatSheaf) ι≅M:=by
  letI:=Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact   (tildeFinsupp (R:=R) ι).symm ≪≫
    (tilde.functor R).mapIso b.repr.symm.toModuleIso ≪≫ asIso M.fromTildeΓ
lemma frame_hom_inv {ι:Type u} (b:Module.Basis ι R (moduleSpecΓFunctor.obj M)):
    (frame M b).hom≫(frame M b).inv=𝟙 _ :=(frame M b).hom_inv_id
lemma frame_inv_hom {ι:Type u} (b:Module.Basis ι R (moduleSpecΓFunctor.obj M)):
    (frame M b).inv≫(frame M b).hom=𝟙 _ :=(frame M b).inv_hom_id
end AffineModuleBasisFrame318
