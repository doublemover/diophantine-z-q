module
public import OriginalLineAutomorphismEquiv318
public import ActualSourceRationalConstants318
public section
noncomputable section
namespace ContactLineAutomorphisms318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev X := ActualSourceRationalConstants318.X

/-- The original structural rational constants are exactly the actual
global regular functions of the original complete contact source. -/
@[expose] def constantsIso : ℚ ≃+* Γ(X,⊤) :=
  RingEquiv.ofBijective ActualSourceRationalConstants318.structuralConstant
    ActualSourceRationalConstants318.constant_bijective

/-- Every original line on the original complete source has the actual
automorphism group Q-star. This uses original global constants and does not
assert universal structure-sheaf pushforward under arbitrary base change. -/
@[expose] def equivalence (L : Line X) : Aut L.object ≃* ℚˣ :=
  (OriginalLineAutomorphismEquiv318.equivalence L).trans
    (Units.mapEquiv constantsIso.toMulEquiv).symm

lemma original_scalar (L : Line X) (f : Aut L.object) :
    ActualSourceRationalConstants318.structuralConstant (equivalence L f).val =
      (OriginalLineAutomorphismScalar318.scalar L f.asIso).val := by
  exact congrArg Units.val ((Units.mapEquiv constantsIso.toMulEquiv).apply_symm_apply
    (OriginalLineAutomorphismEquiv318.equivalence L f))

/-- The classification retains the actual automorphism action on every
original open and section, through the original structural Q action. -/
lemma original_action (L : Line X) (f : Aut L.object) (W : X.Opens) (s : Γ(L.object,W)) :
    f.asIso.hom.app W s =
      X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
        (ActualSourceRationalConstants318.structuralConstant (equivalence L f).val) • s := by
  rw [original_scalar]
  exact OriginalLineAutomorphismScalar318.scalar_action L f.asIso W s
end ContactLineAutomorphisms318
