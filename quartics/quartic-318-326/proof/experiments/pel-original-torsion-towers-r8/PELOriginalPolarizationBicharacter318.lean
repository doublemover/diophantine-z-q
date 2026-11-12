module
public import PELOriginalRelativePolarizationGroupTransformation318
public section
noncomputable section
namespace PELOriginalPolarizationBicharacter318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalSchemePointGroup318 PELOriginalCubeTestClasses318
open PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im) {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))

/-- The normalized polarization class on an arbitrary scheme test.
The actual zero-map pullback is retained, so both axes are genuinely
trivial before passing to any relative quotient. -/
@[expose] def pairing (a b : Points τ hτ Y ρ) : Class Y :=
  value τ hτ ρ (a+b)*(value τ hτ ρ a)⁻¹*(value τ hτ ρ b)⁻¹*value τ hτ ρ 0
lemma symmetric (a b : Points τ hτ Y ρ) : pairing τ hτ ρ a b=pairing τ hτ ρ b a := by
  simp only [pairing,add_comm a b]
  group
lemma zero_left (a : Points τ hτ Y ρ) : pairing τ hτ ρ 0 a=1 := by
  simp only [pairing,zero_add]
  group
lemma zero_right (a : Points τ hτ Y ρ) : pairing τ hτ ρ a 0=1 := by
  rw [symmetric,zero_left]
lemma add_right (a b c : Points τ hτ Y ρ) :
    pairing τ hτ ρ a (b+c)=pairing τ hτ ρ a b*pairing τ hτ ρ a c := by
  have h := cube τ hτ ρ a b c
  rw [add_assoc] at h
  have hsum : value τ hτ ρ (a+(b+c))=
      value τ hτ ρ (a+b)*value τ hτ ρ (a+c)*value τ hτ ρ (b+c)*value τ hτ ρ 0*
      (value τ hτ ρ a)⁻¹*(value τ hτ ρ b)⁻¹*(value τ hτ ρ c)⁻¹ := by
    calc
      _ = (value τ hτ ρ (a+(b+c))*value τ hτ ρ a*value τ hτ ρ b*value τ hτ ρ c)*
        (value τ hτ ρ a)⁻¹*(value τ hτ ρ b)⁻¹*(value τ hτ ρ c)⁻¹ := by group
      _ = _ := by rw [h]
  simp only [pairing]
  rw [hsum]
  group
lemma add_left (a b c : Points τ hτ Y ρ) :
    pairing τ hτ ρ (a+b) c=pairing τ hτ ρ a c*pairing τ hτ ρ b c := by
  rw [symmetric,add_right,symmetric τ hτ ρ c a,symmetric τ hτ ρ c b]

/-- An honest two-variable group homomorphism into actual line classes,
not a merely numerical bilinear pairing. -/
@[expose] def bicharacter : Multiplicative (Points τ hτ Y ρ) →*
    (Multiplicative (Points τ hτ Y ρ) →* Class Y) where
  toFun a := {
    toFun b := pairing τ hτ ρ a.toAdd b.toAdd
    map_one' := zero_right τ hτ ρ a.toAdd
    map_mul' b c := add_right τ hτ ρ a.toAdd b.toAdd c.toAdd }
  map_one' := by ext b; exact zero_left τ hτ ρ b.toAdd
  map_mul' a b := by ext c; exact add_left τ hτ ρ a.toAdd b.toAdd c.toAdd

/-- The class comes from this literal tensor of four actual pullback
line sheaves. No line is introduced solely as a class representative. -/
@[expose] def normalizedLine (a b : Points τ hτ Y ρ) : Line Y :=
  LineSheafTensor318.line
    (LineSheafTensor318.line
      (LineSheafTensor318.line (LineSheafPullback318.line (a+b).val (line τ hτ))
        (FramedLineInverse318.inverse (LineSheafPullback318.line a.val (line τ hτ))))
      (FramedLineInverse318.inverse (LineSheafPullback318.line b.val (line τ hτ))))
    (LineSheafPullback318.line (0 : Points τ hτ Y ρ).val (line τ hτ))
lemma normalizedLine_class (a b : Points τ hτ Y ρ) :
    classOf (normalizedLine τ hτ ρ a b)=pairing τ hτ ρ a b := by
  simp only [normalizedLine,LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse]
  rfl
@[expose] def symmetricIso (a b : Points τ hτ Y ρ) :
    (normalizedLine τ hτ ρ a b).object ≅ (normalizedLine τ hτ ρ b a).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [normalizedLine_class,normalizedLine_class,symmetric]
@[expose] def addRightIso (a b c : Points τ hτ Y ρ) :
    (normalizedLine τ hτ ρ a (b+c)).object ≅
      (LineSheafTensor318.line (normalizedLine τ hτ ρ a b) (normalizedLine τ hτ ρ a c)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafClassGroup318.classOf_tensor,normalizedLine_class,normalizedLine_class,
    normalizedLine_class,add_right]
@[expose] def addLeftIso (a b c : Points τ hτ Y ρ) :
    (normalizedLine τ hτ ρ (a+b) c).object ≅
      (LineSheafTensor318.line (normalizedLine τ hτ ρ a c) (normalizedLine τ hτ ρ b c)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafClassGroup318.classOf_tensor,normalizedLine_class,normalizedLine_class,
    normalizedLine_class,add_left]
@[expose] def zeroLeftIso (a : Points τ hτ Y ρ) :
    (normalizedLine τ hτ ρ 0 a).object ≅ SheafOfModules.unit Y.ringCatSheaf := by
  apply Classical.choice
  apply (LineSheafUnit318.eq_unitClass_iff _).mp
  rw [normalizedLine_class,zero_left]
@[expose] def zeroRightIso (a : Points τ hτ Y ρ) :
    (normalizedLine τ hτ ρ a 0).object ≅ SheafOfModules.unit Y.ringCatSheaf := by
  apply Classical.choice
  apply (LineSheafUnit318.eq_unitClass_iff _).mp
  rw [normalizedLine_class,zero_right]
end PELOriginalPolarizationBicharacter318
