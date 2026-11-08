module
public import IntrinsicDifferentialGlobalScalars318
public section
noncomputable section
namespace StructuralConstantPullback318
open AlgebraicGeometry CategoryTheory
universe u
variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}
/-- Constants use the original structural map and the original Spec/sections
comparison. No extra algebra or scalar action is chosen. -/
@[expose] def constant (p : X ⟶ Spec R) : R →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
/-- An actual over-base square preserves these same structural constants. -/
theorem app_constant (f : X ⟶ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (h : f ≫ q = p) (a : R) :
    f.appTop (constant q a) = constant p a := by
  exact congrArg (fun t : X ⟶ Spec R => t.appTop ((Scheme.ΓSpecIso R).inv a)) h
/-- The original global intrinsic differential pullback respects structural
base constants through the original appTop map, without a default scalar action. -/
theorem globalSection_constant_smul (f : X ⟶ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (h : f ≫ q = p) (a : R) (s : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤)) :
    IntrinsicDifferentialPullback318.globalSection f p q h (constant q a • s) =
      constant p a • IntrinsicDifferentialPullback318.globalSection f p q h s := by
  rw [IntrinsicDifferentialGlobalScalars318.globalSection_smul, app_constant f p q h]
end StructuralConstantPullback318
