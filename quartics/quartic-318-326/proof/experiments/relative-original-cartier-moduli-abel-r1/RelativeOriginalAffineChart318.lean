module
public import RelativeOriginalChartSections318
public import Mathlib.AlgebraicGeometry.Pullbacks
public import LineSheafPullback318
public section
noncomputable section
namespace RelativeOriginalAffineChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open scoped TensorProduct
universe u
variable (k R B : CommRingCat.{u}) [Algebra k R] [Algebra k B]
  {X : Scheme.{u}} (p : X ⟶ Spec k) (j : Spec B ⟶ X)
  (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k B)))
abbrev baseMap := Spec.map (CommRingCat.ofHom (algebraMap k R))
abbrev family := pullback p (baseMap k R)
abbrev ring := CommRingCat.of (R ⊗[k] B)

/-- The actual original affine tensor chart after arbitrary coefficient
base change, retaining the p-FIRST full original test family. -/
def chartIso : pullback j (pullback.fst p (baseMap k R)) ≅ Spec (ring k R B) :=
  pullbackRightPullbackFstIso p (baseMap k R) j ≪≫
    pullback.congrHom hj rfl ≪≫
    pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap k B))) (baseMap k R) ≪≫
    pullbackSpecIso k R B

def into : Spec (ring k R B) ⟶ family k R p :=
  (chartIso k R B p j hj).inv ≫ pullback.snd _ _

instance [IsOpenImmersion j] : IsOpenImmersion (into k R B p j hj) := by
  unfold into
  infer_instance

lemma range [IsOpenImmersion j] : (into k R B p j hj).opensRange =
    (pullback.fst p (baseMap k R)) ⁻¹ᵁ j.opensRange :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (Scheme.Hom.opensRange_pullbackSnd j (pullback.fst p (baseMap k R)))

/-- Exact original coefficient projection of the full new tensor chart. -/
lemma over_test : into k R B p j hj ≫ pullback.snd p (baseMap k R) =
    Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] B))) := by
  simp only [into,chartIso,Iso.trans_inv,Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd,pullback.congrHom_inv,
    pullback.map,pullback.lift_snd,Category.comp_id,
    pullbackSymmetry_inv_comp_snd,pullbackSpecIso_inv_fst']

/-- Exact original chart projection of the same tensor chart. -/
lemma over_original : into k R B p j hj ≫ pullback.fst p (baseMap k R) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := B)).toRingHom) ≫ j := by
  simp only [into,chartIso,Iso.trans_inv,Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_fst,pullback.congrHom_inv,
    pullback.map,pullback.lift_fst_assoc,Category.id_comp,Category.comp_id,
    pullbackSymmetry_inv_comp_fst_assoc,pullbackSpecIso_inv_snd_assoc]
  rfl

variable [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B]
  [Module.Finite (Polynomial k) B] (L : Line (family k R p))

/-- The SAME arbitrary global line on the actual entire base-changed chart. -/
abbrev chartLine := LineSheafPullback318.line (into k R B p j hj) L
abbrev sections := RelativeOriginalChartSections318.sections k R B (chartLine k R B p j hj L)

/-- Finite polynomial sections for an arbitrary original line on the
actual full test curve, derived on its genuine tensor chart. -/
instance finite : Module.Finite (Polynomial R) (sections k R B p j hj L) :=
  RelativeOriginalChartSections318.finite k R B (chartLine k R B p j hj L)
end RelativeOriginalAffineChart318
