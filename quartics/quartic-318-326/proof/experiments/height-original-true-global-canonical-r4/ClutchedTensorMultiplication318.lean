module
public import OpenTensorCoordinates318
public import ClutchedModuleFrames318
public import CocycleTwistedCoordinates318
public section
noncomputable section
namespace ClutchedTensorMultiplication318
open AlgebraicGeometry CategoryTheory Opposite
open ClutchedModule318 ClutchedModuleFrames318 IntrinsicTensorSheaf318
universe u
variable {X Y₀ Y₁ W : Scheme.{u}}
  (j₀ : Y₀ ⟶ X) (j₁ : Y₁ ⟶ X) (k₀ : W ⟶ Y₀) (k₁ : W ⟶ Y₁)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion k₀] [IsOpenImmersion k₁]
  (h : k₁ ≫ j₁ = k₀ ≫ j₀) (a b : Γ(W,⊤)) (ha : IsUnit a) (hb : IsUnit b)
  (hr₀ : j₀ ⁻¹ᵁ j₁.opensRange = k₀.opensRange)
  (hr₁ : j₁ ⁻¹ᵁ j₀.opensRange = k₁.opensRange)
local notation "M" => sheaf j₀ j₁ k₀ k₁ h a
local notation "N" => sheaf j₀ j₁ k₀ k₁ h b

@[expose] def firstCoordinate : tensor M N ⟶ (Scheme.Modules.pushforward j₀).obj (unit Y₀) :=
  OpenTensorCoordinates318.coordinate j₀ M N
    (firstFrame j₀ j₁ k₀ k₁ h a ha hr₁) (firstFrame j₀ j₁ k₀ k₁ h b hb hr₁)
@[expose] def secondCoordinate : tensor M N ⟶ (Scheme.Modules.pushforward j₁).obj (unit Y₁) :=
  OpenTensorCoordinates318.coordinate j₁ M N
    (secondFrame j₀ j₁ k₀ k₁ h a hr₀) (secondFrame j₀ j₁ k₀ k₁ h b hr₀)

lemma first_pure (V : X.Opens) (m : Γ(M,V)) (n : Γ(N,V)) :
    (firstCoordinate j₀ j₁ k₀ k₁ h a b ha hb hr₁).app V (pure M N V m n) =
      (first j₀ j₁ k₀ k₁ h a).app V m * (first j₀ j₁ k₀ k₁ h b).app V n := by
  rw [firstCoordinate,OpenTensorCoordinates318.coordinate_pure]
  have ea : (Scheme.Modules.restrictAdjunction j₀).homEquiv M (unit Y₀)
      (firstFrame j₀ j₁ k₀ k₁ h a ha hr₁).hom = first j₀ j₁ k₀ k₁ h a :=
    Equiv.apply_symm_apply _ _
  have eb : (Scheme.Modules.restrictAdjunction j₀).homEquiv N (unit Y₀)
      (firstFrame j₀ j₁ k₀ k₁ h b hb hr₁).hom = first j₀ j₁ k₀ k₁ h b :=
    Equiv.apply_symm_apply _ _
  rw [ea,eb]

lemma second_pure (V : X.Opens) (m : Γ(M,V)) (n : Γ(N,V)) :
    (secondCoordinate j₀ j₁ k₀ k₁ h a b hr₀).app V (pure M N V m n) =
      (second j₀ j₁ k₀ k₁ h a).app V m * (second j₀ j₁ k₀ k₁ h b).app V n := by
  rw [secondCoordinate,OpenTensorCoordinates318.coordinate_pure]
  have ea : (Scheme.Modules.restrictAdjunction j₁).homEquiv M (unit Y₁)
      (secondFrame j₀ j₁ k₀ k₁ h a hr₀).hom = second j₀ j₁ k₀ k₁ h a :=
    Equiv.apply_symm_apply _ _
  have eb : (Scheme.Modules.restrictAdjunction j₁).homEquiv N (unit Y₁)
      (secondFrame j₀ j₁ k₀ k₁ h b hr₀).hom = second j₀ j₁ k₀ k₁ h b :=
    Equiv.apply_symm_apply _ _
  rw [ea,eb]

/-- Multiplication retains the actual full intersection, its exact route
identification and the product transition; no pointwise gluing is used. -/
lemma compatible :
    firstCoordinate j₀ j₁ k₀ k₁ h a b ha hb hr₁ ≫ restriction j₀ k₀ =
      secondCoordinate j₀ j₁ k₀ k₁ h a b hr₀ ≫
        twistedRestriction j₀ j₁ k₀ k₁ h (a*b) := by
  apply OpenTensorCoordinates318.hom_ext M N
  intro V m n
  let e : (k₀ ≫ j₀) ⁻¹ᵁ V = (k₁ ≫ j₁) ⁻¹ᵁ V := by rw [h]
  have hm := congrArg (fun f => f.app V m) (compatibility j₀ j₁ k₀ k₁ h a)
  have hn := congrArg (fun f => f.app V n) (compatibility j₀ j₁ k₀ k₁ h b)
  change k₀.app (j₀ ⁻¹ᵁ V) ((first j₀ j₁ k₀ k₁ h a).app V m) = _ at hm
  change k₀.app (j₀ ⁻¹ᵁ V) ((first j₀ j₁ k₀ k₁ h b).app V n) = _ at hn
  rw [CocycleTwistedCoordinates318.twisted_app _ _ _ _ _ _ _ e] at hm hn
  change k₀.app (j₀ ⁻¹ᵁ V)
    ((firstCoordinate j₀ j₁ k₀ k₁ h a b ha hb hr₁).app V (pure M N V m n)) =
    (twistedRestriction j₀ j₁ k₀ k₁ h (a*b)).app V
      ((secondCoordinate j₀ j₁ k₀ k₁ h a b hr₀).app V (pure M N V m n))
  rw [first_pure,second_pure,map_mul,hm,hn,
    CocycleTwistedCoordinates318.twisted_app _ _ _ _ _ _ _ e]
  simp only [map_mul]
  ring

/-- A genuine map FROM the sheafified intrinsic tensor product into the
unchanged clutched product-transition sheaf. -/
@[expose] def multiplication : tensor M N ⟶ sheaf j₀ j₁ k₀ k₁ h (a*b) :=
  lift j₀ j₁ k₀ k₁ h (a*b)
    (firstCoordinate j₀ j₁ k₀ k₁ h a b ha hb hr₁)
    (secondCoordinate j₀ j₁ k₀ k₁ h a b hr₀)
    (compatible j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁)

lemma multiplication_first :
    multiplication j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ ≫ first j₀ j₁ k₀ k₁ h (a*b) =
      firstCoordinate j₀ j₁ k₀ k₁ h a b ha hb hr₁ := lift_first _ _ _ _ _ _ _ _ _
lemma multiplication_second :
    multiplication j₀ j₁ k₀ k₁ h a b ha hb hr₀ hr₁ ≫ second j₀ j₁ k₀ k₁ h (a*b) =
      secondCoordinate j₀ j₁ k₀ k₁ h a b hr₀ := lift_second _ _ _ _ _ _ _ _ _
end ClutchedTensorMultiplication318
