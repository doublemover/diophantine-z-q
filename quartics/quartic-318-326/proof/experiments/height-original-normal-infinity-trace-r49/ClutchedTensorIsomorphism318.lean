module
public import ClutchedTensorMultiplication318
public import OpenImmersionModuleIsoCriterion318
public section
noncomputable section
namespace ClutchedTensorIsomorphism318
open AlgebraicGeometry CategoryTheory
open ClutchedModule318 ClutchedModuleFrames318 ClutchedTensorMultiplication318
open IntrinsicTensorSheaf318
universe u
variable {X Y₀ Y₁ W : Scheme.{u}}
  (j₀ : Y₀ ⟶ X) (j₁ : Y₁ ⟶ X) (k₀ : W ⟶ Y₀) (k₁ : W ⟶ Y₁)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion k₀] [IsOpenImmersion k₁]
  (h : k₁ ≫ j₁ = k₀ ≫ j₀) (a b : Γ(W,⊤)) (ha : IsUnit a) (hb : IsUnit b)
  (hr₀ : j₀ ⁻¹ᵁ j₁.opensRange = k₀.opensRange)
  (hr₁ : j₁ ⁻¹ᵁ j₀.opensRange = k₁.opensRange)
local notation "M" => sheaf j₀ j₁ k₀ k₁ h a
local notation "N" => sheaf j₀ j₁ k₀ k₁ h b
local notation "μ" => multiplication j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁

/-- Exact whole-chart equation for the original constructed multiplication. -/
lemma first_frame :
    (Scheme.Modules.restrictFunctor j₀).map μ ≫
      (firstFrame j₀ j₁ k₀ k₁ h (a*b) (ha.mul hb) hr₁).hom =
    (OpenTensorCoordinates318.frame j₀ M N
      (firstFrame j₀ j₁ k₀ k₁ h a ha hr₁)
      (firstFrame j₀ j₁ k₀ k₁ h b hb hr₁)).hom := by
  change (Scheme.Modules.restrictFunctor j₀).map μ ≫
    ((Scheme.Modules.restrictAdjunction j₀).homEquiv _ _).symm
      (first j₀ j₁ k₀ k₁ h (a*b)) = _
  rw [←Adjunction.homEquiv_naturality_left_symm,multiplication_first]
  exact OpenTensorCoordinates318.transpose _ _ _ _ _

lemma second_frame :
    (Scheme.Modules.restrictFunctor j₁).map μ ≫
      (secondFrame j₀ j₁ k₀ k₁ h (a*b) hr₀).hom =
    (OpenTensorCoordinates318.frame j₁ M N
      (secondFrame j₀ j₁ k₀ k₁ h a hr₀)
      (secondFrame j₀ j₁ k₀ k₁ h b hr₀)).hom := by
  change (Scheme.Modules.restrictFunctor j₁).map μ ≫
    ((Scheme.Modules.restrictAdjunction j₁).homEquiv _ _).symm
      (second j₀ j₁ k₀ k₁ h (a*b)) = _
  rw [←Adjunction.homEquiv_naturality_left_symm,multiplication_second]
  exact OpenTensorCoordinates318.transpose _ _ _ _ _

variable (hc : j₀.opensRange ⊔ j₁.opensRange = ⊤)
include hc in
lemma multiplication_isIso : IsIso μ := by
  apply ModuleFrameDescent318.isIso_of_cover
    (fun i : ULift.{u} Bool => if i.down then j₀.opensRange else j₁.opensRange)
    (by
      intro x _
      have hx : x ∈ j₀.opensRange ⊔ j₁.opensRange := by rw [hc]; trivial
      rcases hx with hx | hx
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨true⟩,hx⟩
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨false⟩,hx⟩)
  intro i V hV
  rcases i with ⟨i⟩
  cases i
  · letI : IsIso ((Scheme.Modules.restrictFunctor j₁).map μ ≫
        (secondFrame j₀ j₁ k₀ k₁ h (a*b) hr₀).hom) := by
      rw [second_frame]
      infer_instance
    letI : IsIso ((Scheme.Modules.restrictFunctor j₁).map μ) :=
      IsIso.of_isIso_comp_right _ (secondFrame j₀ j₁ k₀ k₁ h (a*b) hr₀).hom
    exact OpenImmersionModuleIsoCriterion318.app_isIso μ j₁ V hV
  · letI : IsIso ((Scheme.Modules.restrictFunctor j₀).map μ ≫
        (firstFrame j₀ j₁ k₀ k₁ h (a*b) (ha.mul hb) hr₁).hom) := by
      rw [first_frame]
      infer_instance
    letI : IsIso ((Scheme.Modules.restrictFunctor j₀).map μ) :=
      IsIso.of_isIso_comp_right _ (firstFrame j₀ j₁ k₀ k₁ h (a*b) (ha.mul hb) hr₁).hom
    exact OpenImmersionModuleIsoCriterion318.app_isIso μ j₀ V hV

/-- Actual intrinsic tensor product of the two unchanged clutched sheaves,
with genuine categorical inverse, not a transition-only identification. -/
@[expose] def iso : tensor M N ≅ sheaf j₀ j₁ k₀ k₁ h (a*b) := by
  letI := multiplication_isIso j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc
  exact asIso μ

lemma hom_first :
    (iso j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc).hom ≫ first j₀ j₁ k₀ k₁ h (a*b) =
      firstCoordinate j₀ j₁ k₀ k₁ h a b ha hb hr₁ :=
  multiplication_first _ _ _ _ _ _ _ _ _ _ _
lemma hom_second :
    (iso j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc).hom ≫ second j₀ j₁ k₀ k₁ h (a*b) =
      secondCoordinate j₀ j₁ k₀ k₁ h a b hr₀ :=
  multiplication_second _ _ _ _ _ _ _ _ _ _ _

/-- Equality transport changes only the literal transition expression, not
its underlying charts or the two projection maps. -/
@[expose] def isoTo (c : Γ(W,⊤)) (he : a*b=c) : tensor M N ≅ sheaf j₀ j₁ k₀ k₁ h c :=
  iso j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc ≪≫
    eqToIso (congrArg (sheaf j₀ j₁ k₀ k₁ h) he)

lemma isoTo_first (c : Γ(W,⊤)) (he : a*b=c) :
    (isoTo j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc c he).hom ≫ first j₀ j₁ k₀ k₁ h c =
      firstCoordinate j₀ j₁ k₀ k₁ h a b ha hb hr₁ := by
  subst c
  simpa only [isoTo,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,Category.comp_id] using
    hom_first j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc

lemma isoTo_second (c : Γ(W,⊤)) (he : a*b=c) :
    (isoTo j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc c he).hom ≫ second j₀ j₁ k₀ k₁ h c =
      secondCoordinate j₀ j₁ k₀ k₁ h a b hr₀ := by
  subst c
  simpa only [isoTo,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,Category.comp_id] using
    hom_second j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ hc
end ClutchedTensorIsomorphism318
