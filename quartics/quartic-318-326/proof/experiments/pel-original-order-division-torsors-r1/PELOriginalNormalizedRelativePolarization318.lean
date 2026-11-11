module
public import PELOriginalNormalizedFamilyBiadditivity318
public section
noncomputable section
namespace PELOriginalNormalizedRelativePolarization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 Opposite
open PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
open PELOriginalCubeTestClasses318 PELOriginalPolarizationBicharacter318
open PELOriginalNormalizedPolarizationFamily318
open RelativeLineClassQuotient318 RelativeLineClassBaseChange318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The zero-normalized symmetric family induces exactly the SAME
relative polarization as m*L tensor inverse(pr1*L). The two extra line
factors are literal parameter pullbacks, killed in the actual quotient
before sheafification. -/
lemma relative_class :
    classMap (pullback.snd (π τ hτ) (π τ hτ)) (classOf (family τ hτ))=
      classMap (pullback.snd (π τ hτ) (π τ hτ))
        (classOf (PELOriginalTranslationDifferenceFamily318.family τ hτ)) := by
  let ρ := baseMap τ hτ
  let a := firstPoint τ hτ
  let b := secondPoint τ hτ
  let Q := classMap (pullback.snd (π τ hτ) (π τ hτ))
  have hb : Q (value τ hτ ρ b)=1 :=
    base_class_trivial (pullback.snd (π τ hτ) (π τ hτ))
      (classOf (PELOriginalAlgebraicPolarizationLine318.line τ hτ))
  have hzero : Q (value τ hτ ρ (0 : Points τ hτ (Product τ hτ) ρ))=1 := by
    have hv : value τ hτ ρ (0 : Points τ hτ (Product τ hτ) ρ)=
        LineClassPullbackHom318.pullback (pullback.snd (π τ hτ) (π τ hτ))
          (value τ hτ (π τ hτ) (0 : Points τ hτ _ (π τ hτ))) := by
      have hp := value_pull τ hτ (π τ hτ) (pullback.snd (π τ hτ) (π τ hτ))
        pullback.condition.symm (0 : Points τ hτ _ (π τ hτ))
      simpa only [map_zero] using hp.symm
    rw [hv]
    exact base_class_trivial _ _
  have hfamily : classOf (PELOriginalTranslationDifferenceFamily318.family τ hτ)=
      value τ hτ ρ (a+b)*(value τ hτ ρ a)⁻¹ := by
    have hlift : pullback.lift a.val b.val (a.property.trans b.property.symm)=𝟙 (Product τ hτ) := by
      apply pullback.hom_ext <;> simp only [pullback.lift_fst,pullback.lift_snd,Category.id_comp]
      all_goals rfl
    have hsum : (a+b).val=PELOriginalAdditionSchemeMorphism318.addition τ hτ := by
      change pullback.lift a.val b.val (a.property.trans b.property.symm)≫_=_
      rw [hlift,Category.id_comp]
    rw [PELOriginalTranslationDifferenceFamily318.family,
      LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse]
    change _=LineClassPullbackHom318.pullback (a+b).val _*(value τ hτ ρ a)⁻¹
    rw [hsum]
    rfl
  change Q (classOf (normalizedLine τ hτ ρ a b))=_
  rw [normalizedLine_class,pairing,hfamily]
  simp only [map_mul,map_inv,hb,hzero,inv_one,mul_one]

lemma transformation_eq :
    OriginalLineAbelTransformation318.transformation (π τ hτ) (π τ hτ) (family τ hτ)=
      PELOriginalRelativePolarizationTransformation318.transformation τ hτ := by
  apply NatTrans.ext
  intro T
  funext a
  change (RelativeFppfLineSheaf318.unit (π τ hτ)).app T
      (testMap (π τ hτ) (π τ hτ) T.unop.hom a.left a.w
        (classMap (pullback.snd (π τ hτ) (π τ hτ)) (classOf (family τ hτ))))=_
  rw [relative_class]
  rfl
end PELOriginalNormalizedRelativePolarization318
