module
public import OriginalLineAutPullback318
public import ContactLineAutomorphisms318
public import RationalContactPoint318
public section
noncomputable section
namespace ContactPointRigidifiedAut318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev X := ContactLineAutomorphisms318.X

/-- Evaluation at any actual field-valued point is injective on the actual
global functions of the original complete source. The proof uses exactly
the original structural Q constants, not a rational-point assumption. -/
lemma fieldPoint_appTop_injective {K : Type} [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X) : Function.Injective p.appTop := by
  intro a b h
  obtain ⟨q, rfl⟩ := ActualSourceRationalConstants318.constant_bijective.surjective a
  obtain ⟨r, rfl⟩ := ActualSourceRationalConstants318.constant_bijective.surjective b
  let e : ℚ →+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
    (p.appTop.hom.comp ActualSourceRationalConstants318.structuralConstant)
  have he : e q = e r := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom h
  exact congrArg ActualSourceRationalConstants318.structuralConstant (e.injective he)

/-- Faithfulness uses the exact actual finite-extension point of the same
source, not a separately chosen abstract evaluation functional. -/
lemma actual_point_faithful (L : Line X) (t : ℚ) : Function.Injective
    ((Scheme.Modules.pullback
      (RationalContactPoint318.point SourceTwistArithmetic318.units t)).mapAut L.object) :=
  OriginalLineAutPullback318.pullbackAut_injective _ L (fieldPoint_appTop_injective _)

/-- For an original source line with an actual trivialization at the actual
finite-extension point, every compatible actual automorphism is identity.
This is not asserted for arbitrary new lines on arbitrary base families. -/
lemma actual_rigidified_aut_eq_one (L : Line X) (t : ℚ) (f : Aut L.object)
    (r : (LineSheafPullback318.line
        (RationalContactPoint318.point SourceTwistArithmetic318.units t) L).object ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of
          (RationalContactPoint318.PointField SourceTwistArithmetic318.units t))).ringCatSheaf)
    (hr : ((Scheme.Modules.pullback
        (RationalContactPoint318.point SourceTwistArithmetic318.units t)).mapAut L.object f).asIso.hom ≫
      r.hom = r.hom) : f = 1 :=
  OriginalLineAutPullback318.rigidified_aut_eq_one _ L (fieldPoint_appTop_injective _) f r hr
end ContactPointRigidifiedAut318
