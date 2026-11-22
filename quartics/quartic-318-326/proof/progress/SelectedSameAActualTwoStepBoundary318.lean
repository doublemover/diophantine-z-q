module

public import SelectedSameASignedCoverInjectiveJoin318

/-! Two genuine connecting boundaries in the literal additive site.
Factor the first row into the fixed injective presentation of its
kernel, and the second into the fixed presentation of the first
quotient. The degree-two class comes from the actual global image
of the given degree-zero section, not an input Čech reflector. -/
public section
noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAActualTwoStepBoundary318

open SelectedSameAActualLiftDifference318 (Sh)
open SelectedSameALiteralInjectiveRow318 (factor factor_left target target_shortExact boundary_eq)
open SelectedSameAGenuineBoundaryLifts318 (boundary)
open SelectedSameASignedLiftCocycle318 (res coeff)
open SelectedSameASignedCoverInjectiveJoin318 (factor_cover_coeff)

universe u w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{u}) {S D : ShortComplex (Sh X)} (hS : S.ShortExact)
variable (hD : D.ShortExact) (alpha : D.X₁ ⟶ S.X₃)

abbrev I₀ := target X S.X₁
abbrev I₁ := target X (I₀ X (S := S)).X₃

/-- Quotient arrow determined by the actual commutative injective row
comparison with identity on the left. -/
def quotientArrow : S.X₃ ⟶ (I₀ X (S := S)).X₃ :=
  (factor X hS (𝟙 S.X₁)).τ₃

abbrev imageLeft : D.X₁ ⟶ (I₀ X (S := S)).X₃ := alpha ≫ quotientArrow X hS

abbrev secondFactor : D ⟶ I₁ X (S := S) :=
  factor X hD (imageLeft X hS alpha)

def imageSection (z : D.X₃.obj.obj (op (⊤ : Opens X))) :
    (I₁ X (S := S)).X₃.obj.obj (op (⊤ : Opens X)) :=
  (secondFactor X hS hD alpha).τ₃.hom.app (op (⊤ : Opens X)) z

section Cover

variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable {I : Type u} (U : I → Opens X)

def imageLift (t : ∀ i, D.X₂.obj.obj (op (U i))) (i : I) :
    (I₁ X (S := S)).X₂.obj.obj (op (U i)) :=
  (secondFactor X hS hD alpha).τ₂.hom.app (op (U i)) (t i)

/-- The new global section in the second injective quotient has
the explicit images of the ORIGINAL local lifts. Its first signed
coordinates are the actual quotient images of the old coordinates. -/
theorem image_lift_and_coefficient
    (z : D.X₃.obj.obj (op (⊤ : Opens X))) (t : ∀ i, D.X₂.obj.obj (op (U i)))
    (ht : ∀ i, D.g.hom.app (op (U i)) (t i) = res X D.X₃ le_top z) :
    let T := I₁ X (S := S)
    let hs := target_shortExact X (I₀ X (S := S)).X₃
    let w := imageSection X hS hD alpha z
    let v := imageLift X hS hD alpha U t
    ∃ hv : ∀ i, T.g.hom.app (op (U i)) (v i) = res X T.X₃ le_top w,
      ∀ i j, coeff X T hs U w v hv i j =
        (imageLeft X hS alpha).hom.app (op (U i ⊓ U j)) (coeff X D hD U z t ht i j) :=
  factor_cover_coeff X hD (imageLeft X hS alpha) U z t ht

end Cover

variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{w} (Sh X)]

/-- Actual degree-two class, in the original left sheaf's H².
The cohomology degrees follow from applying consecutive boundaries
to the single explicit terminal section of the second quotient. -/
def doubleBoundary (z : D.X₃.obj.obj (op (⊤ : Opens X))) : S.X₁.H 2 :=
  Sheaf.H.δ (target_shortExact X S.X₁) 1 2 rfl
    (boundary X (target_shortExact X (I₀ X (S := S)).X₃)
      (imageSection X hS hD alpha z))

/-- Dimension shifting in the actual original sheaf category. No
vanishing, representability, or resolution comparison is assumed.
Both equalities are exact-category naturality for specified row maps. -/
theorem double_boundary_eq_actual (z : D.X₃.obj.obj (op (⊤ : Opens X))) :
    doubleBoundary X hS hD alpha z =
      Sheaf.H.δ hS 1 2 rfl (Sheaf.H.map alpha 1 (boundary X hD z)) := by
  let h₀ := target_shortExact X S.X₁
  let h₁ := target_shortExact X (I₀ X (S := S)).X₃
  let b : S.X₃.H 1 := Sheaf.H.map alpha 1 (boundary X hD z)
  have hImage :
      boundary X h₁ (imageSection X hS hD alpha z) =
        Sheaf.H.map (imageLeft X hS alpha) 1 (boundary X hD z) :=
    boundary_eq X hD (imageLeft X hS alpha) z
  have hNat :=
    Sheaf.H.δ_naturality 1 2 rfl hS h₀ (factor X hS (𝟙 S.X₁)) b
  rw [factor_left] at hNat
  have hId : Sheaf.H.map (𝟙 S.X₁) 2 (Sheaf.H.δ hS 1 2 rfl b) =
      Sheaf.H.δ hS 1 2 rfl b :=
    Sheaf.H.map_id_apply (Sheaf.H.δ hS 1 2 rfl b)
  have hNat' : Sheaf.H.δ h₀ 1 2 rfl
      (Sheaf.H.map (quotientArrow X hS) 1 b) = Sheaf.H.δ hS 1 2 rfl b :=
    Eq.trans hNat hId
  have hImage' : boundary X h₁ (imageSection X hS hD alpha z) =
      Sheaf.H.map (quotientArrow X hS) 1 b :=
    hImage.trans (Sheaf.H.map_comp_apply alpha (quotientArrow X hS) (boundary X hD z))
  exact Eq.trans (congrArg (Sheaf.H.δ h₀ 1 2 rfl) hImage') hNat'

end SelectedSameAActualTwoStepBoundary318
