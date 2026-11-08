module
public import IntrinsicDifferentialPullback318
public section
noncomputable section
namespace IntrinsicDifferentialGlobalScalars318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
  (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (h : f ≫ q = p)

/-- The original global intrinsic differential pullback is semilinear for
exactly the original global section map. No generic localization, chart,
flatness or reducedness assumption is used. -/
theorem globalSection_smul (a : Γ(Y, ⊤))
    (s : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤)) :
    IntrinsicDifferentialPullback318.globalSection f p q h (a • s) =
      f.appTop a • IntrinsicDifferentialPullback318.globalSection f p q h s := by
  change (IntrinsicDifferentialPullback318.map f p q h).val.app (op ⊤) (a • s) =
    a • ((IntrinsicDifferentialPullback318.map f p q h).val.app (op ⊤) s)
  exact map_smul _ a s

end IntrinsicDifferentialGlobalScalars318
