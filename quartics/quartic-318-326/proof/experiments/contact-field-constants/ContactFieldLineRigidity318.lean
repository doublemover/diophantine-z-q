module
public import ContactFieldConstants318
public import OriginalLineAutPullback318
public import ContactFieldSection318
public section
noncomputable section
namespace ContactFieldLineRigidity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
abbrev X := ContactFieldConstants318.Family K c

/-- This is the automorphism group of every actual line on the entire
field-base-changed source, including lines not pulled back from Q. -/
@[expose] def equivalence (L : Line (X K c)) : Aut L.object ≃* Kˣ :=
  (OriginalLineAutomorphismEquiv318.equivalence L).trans
    (Units.mapEquiv (ContactFieldConstants318.constantsIso K c).toMulEquiv).symm

lemma original_scalar (L : Line (X K c)) (f : Aut L.object) :
    ContactFieldConstants318.structuralMap K c (equivalence K c L f).val =
      (OriginalLineAutomorphismScalar318.scalar L f.asIso).val := by
  exact congrArg Units.val ((Units.mapEquiv
    (ContactFieldConstants318.constantsIso K c).toMulEquiv).apply_symm_apply
      (OriginalLineAutomorphismEquiv318.equivalence L f))

lemma original_action (L : Line (X K c)) (f : Aut L.object)
    (W : (X K c).Opens) (s : Γ(L.object, W)) :
    f.asIso.hom.app W s =
      (X K c).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
        (ContactFieldConstants318.structuralMap K c (equivalence K c L f).val) • s := by
  rw [original_scalar]
  exact OriginalLineAutomorphismScalar318.scalar_action L f.asIso W s

/-- Any actual field point detects automorphisms of every actual line on
this whole field base change. No existence of a K-point is assumed here. -/
lemma point_faithful {F : Type} [Field F] (p : Spec (CommRingCat.of F) ⟶ X K c)
    (L : Line (X K c)) : Function.Injective ((Scheme.Modules.pullback p).mapAut L.object) :=
  OriginalLineAutPullback318.pullbackAut_injective p L
    (ContactFieldConstants318.fieldPoint_appTop_injective K c p)

/-- For the existing explicit contact field and its actual source section,
rigidification eliminates every actual line automorphism, including lines
newly defined on the full field family. -/
lemma contact_section_rigidified_aut_eq_one (t : ℚ)
    (L : Line (X (ContactFieldSection318.L c t) c)) (f : Aut L.object)
    (r : (LineSheafPullback318.line (ContactFieldSection318.pointSection c t) L).object ≅
      SheafOfModules.unit (ContactFieldSection318.FieldBase c t).ringCatSheaf)
    (hr : ((Scheme.Modules.pullback (ContactFieldSection318.pointSection c t)).mapAut
      L.object f).asIso.hom ≫ r.hom = r.hom) : f = 1 :=
  OriginalLineAutPullback318.rigidified_aut_eq_one _ L
    (ContactFieldConstants318.fieldPoint_appTop_injective _ c _) f r hr
end ContactFieldLineRigidity318
