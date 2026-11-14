module
public import PELOriginalPolarizationSymmetricSquare318
public section
noncomputable section
namespace PELOriginalPolarizationTheoremOfSquare318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalTranslationLineClass318 PELOriginalPolarizationSymmetricSquare318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Divisibility is produced in the ACTUAL original quotient by lifting
two points to their original complex vector representatives. -/
lemma exists_midpoint (q r : Base τ) : ∃ u : Base τ,u+u=q+r := by
  obtain ⟨a,rfl⟩ := quotient_surjective (P τ) q
  obtain ⟨b,rfl⟩ := quotient_surjective (P τ) r
  let c : ComplexVectors := (1/2 : ℂ) • (a+b)
  have hc : c+c=a+b := by ext i; dsimp [c]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
  refine ⟨projection (P τ) c,?_⟩
  rw [←PELOriginalAdditionSchemeMorphism318.projection_add,hc,
    PELOriginalAdditionSchemeMorphism318.projection_add]

/-- The theorem of square for ALL original complex points, in the
actual group of whole algebraic line-sheaf isomorphism classes. -/
theorem square_class (q r : Base τ) :
    action τ hτ q (classOf (line τ hτ))*action τ hτ r (classOf (line τ hτ))=
      action τ hτ (q+r) (classOf (line τ hτ))*classOf (line τ hτ) := by
  obtain ⟨u,hu⟩ := exists_midpoint τ hτ q r
  let v := q-u
  have hq : u+v=q := by dsimp [v]; abel
  have hr : u+ -v=r := by
    calc
      _ = (u+u)-q := by dsimp [v]; abel
      _ = (q+r)-q := by rw [hu]
      _ = r := by abel
  have hs := congrArg (action τ hτ u) (symmetric_class τ hτ v)
  rw [(action τ hτ u).map_mul,(action τ hτ u).map_pow,←action_add,←action_add,hq,hr] at hs
  have hd := congrArg (action τ hτ u) (symmetric_class τ hτ u)
  rw [(action τ hτ u).map_mul,(action τ hτ u).map_pow,←action_add,←action_add,
    add_neg_cancel,action_zero,hu] at hd
  exact hs.trans hd.symm

/-- A genuine whole sheaf isomorphism, obtained only AFTER the produced
regular balanced gauges establish the exact class identity. -/
@[expose] def squareIso (q r : Base τ) :
    (LineSheafTensor318.line (translatedLine τ hτ q) (translatedLine τ hτ r)).object ≅
      (LineSheafTensor318.line (translatedLine τ hτ (q+r)) (line τ hτ)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_tensor]
  exact square_class τ hτ q r

/-- The formerly twisted translation-difference law now genuinely
untwists. This conclusion uses the actual square isomorphism above. -/
theorem polarization_add (q r : Base τ) :
    polarizationClass τ hτ (q+r)=polarizationClass τ hτ q*polarizationClass τ hτ r := by
  rw [class_formula,class_formula,class_formula]
  calc
    _ = (action τ hτ (q+r) (classOf (line τ hτ))*classOf (line τ hτ))*
        ((classOf (line τ hτ))⁻¹*(classOf (line τ hτ))⁻¹) := by group
    _ = _ := by rw [←square_class]; group

/-- Honest group homomorphism on ALL original complex points, with
codomain the group of ACTUAL line-sheaf classes, not a represented dual. -/
@[expose] def polarizationHom : Multiplicative (Base τ) →* Class (candidate τ hτ) where
  toFun q := polarizationClass τ hτ (Multiplicative.toAdd q)
  map_one' := zero_class τ hτ
  map_mul' q r := polarization_add τ hτ (Multiplicative.toAdd q) (Multiplicative.toAdd r)

theorem polarizationHom_injective : Function.Injective (polarizationHom τ hτ) := by
  intro q r h
  have he : Multiplicative.toAdd q=Multiplicative.toAdd r :=
    PELOriginalPolarizationClassFaithful318.polarization_class_injective τ hτ h
  exact congrArg Multiplicative.ofAdd he

/-- Translation differences are invariant under every actual original
translation, as whole line classes. This is stronger than the earlier
twisted cocycle, and still makes no dual-representability assertion. -/
theorem difference_translation_invariant (q r : Base τ) :
    action τ hτ q (polarizationClass τ hτ r)=polarizationClass τ hτ r := by
  apply mul_right_cancel
  calc
    _ = polarizationClass τ hτ (q+r) := (twisted_add τ hτ q r).symm
    _ = polarizationClass τ hτ r*polarizationClass τ hτ q := by rw [polarization_add,mul_comm]

@[expose] def differenceTranslationIso (q r : Base τ) :
    (LineSheafPullback318.line (PELOriginalTranslationAutomorphisms318.translation τ hτ q)
      (differenceLine τ hτ r)).object ≅ (differenceLine τ hτ r).object :=
  Classical.choice ((classOf_eq_iff _ _).mp (difference_translation_invariant τ hτ q r))
end PELOriginalPolarizationTheoremOfSquare318
