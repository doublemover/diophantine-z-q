module
public import ContactOriginalPositiveBaseCoordinates318
public import OriginalGlobalFrameGenerator318
public import OriginalModuleTwoOpenGluing318
public section
noncomputable section
namespace ContactOriginalPositiveGlobalSections318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalTwistingLine318
open ContactOriginalPositiveBaseCoordinates318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
abbrev M := (line c 1).object

def finite (V : (X c).Opens) (hV : V ≤ finiteOpen c) :=
  OpenLineFrameCoordinates318.frame (M c) (finiteOpen c) (finiteFrame c 1).symm V hV

def infinity (V : (X c).Opens) (hV : V ≤ infinityOpen c) :=
  OpenLineFrameCoordinates318.frame (M c) (infinityOpen c) (infinityFrame c 1).symm V hV

/-- Gluing actual original frame coefficients, using their proved original
T transition and the genuine full-open sheaf condition. -/
lemma exists_section (a : Γ(X c,finiteOpen c)) (b : Γ(X c,infinityOpen c))
    (h : (X c).presheaf.map (homOfLE inf_le_left).op a =
      (X c).presheaf.map (homOfLE inf_le_right).op b * scalar c (LaurentPolynomial.T 1)) :
    ∃ s : Γ(M c,⊤),
      (M c).presheaf.map (homOfLE (show finiteOpen c ≤ ⊤ from le_top)).op s =
        finite c (finiteOpen c) le_rfl a ∧
      (M c).presheaf.map (homOfLE (show infinityOpen c ≤ ⊤ from le_top)).op s =
        infinity c (infinityOpen c) le_rfl b := by
  apply OriginalModuleTwoOpenGluing318.exists_gluing (M c) (finiteOpen c) (infinityOpen c) (cover c)
  apply (finite c (finiteOpen c ⊓ infinityOpen c) inf_le_left).symm.injective
  change (OpenLineFrameCoordinates318.frame (M c) (finiteOpen c) (finiteFrame c 1).symm _ _).symm _ =
    (OpenLineFrameCoordinates318.frame (M c) (finiteOpen c) (finiteFrame c 1).symm _ _).symm _
  have hf := OpenLineFrameCoordinates318.inverse_natural (M c) (finiteOpen c)
    (finiteFrame c 1).symm le_rfl inf_le_left (finite c (finiteOpen c) le_rfl a)
  have hi := OpenLineFrameCoordinates318.inverse_natural (M c) (infinityOpen c)
    (infinityFrame c 1).symm le_rfl inf_le_right (infinity c (infinityOpen c) le_rfl b)
  simp only [finite,infinity,LinearEquiv.symm_apply_apply] at hf hi
  have hc := ContactOriginalTwistTransition318.inverse_relation c 1
    ((M c).presheaf.map (homOfLE inf_le_right).op (infinity c (infinityOpen c) le_rfl b))
  exact hf.symm.trans (h.trans
    ((congrArg (fun z => z * scalar c (LaurentPolynomial.T 1)) hi).trans hc.symm))

lemma zero_compatible : (X c).presheaf.map (homOfLE inf_le_left).op (1 : Γ(X c,finiteOpen c)) =
    (X c).presheaf.map (homOfLE inf_le_right).op (infinityCoordinate c) *
      scalar c (LaurentPolynomial.T 1) := by
  rw [map_one,infinity_restriction,← map_mul,← LaurentPolynomial.T_add]
  norm_num

lemma one_compatible : (X c).presheaf.map (homOfLE inf_le_left).op (finiteCoordinate c) =
    (X c).presheaf.map (homOfLE inf_le_right).op (1 : Γ(X c,infinityOpen c)) *
      scalar c (LaurentPolynomial.T 1) := by
  rw [finite_restriction,map_one,one_mul]

/-- Actual original global sections with finite/infinity coefficients
(1,u) and (t,1), not rational sections subsequently asserted regular. -/
def zero : Γ(M c,⊤) := Classical.choose (exists_section c 1 (infinityCoordinate c) (zero_compatible c))
def one : Γ(M c,⊤) := Classical.choose (exists_section c (finiteCoordinate c) 1 (one_compatible c))

lemma zero_finite : (M c).presheaf.map (homOfLE (show finiteOpen c ≤ ⊤ from le_top)).op (zero c) =
    finite c (finiteOpen c) le_rfl 1 :=
  (Classical.choose_spec (exists_section c 1 (infinityCoordinate c) (zero_compatible c))).1
lemma zero_infinity : (M c).presheaf.map (homOfLE (show infinityOpen c ≤ ⊤ from le_top)).op (zero c) =
    infinity c (infinityOpen c) le_rfl (infinityCoordinate c) :=
  (Classical.choose_spec (exists_section c 1 (infinityCoordinate c) (zero_compatible c))).2
lemma one_finite : (M c).presheaf.map (homOfLE (show finiteOpen c ≤ ⊤ from le_top)).op (one c) =
    finite c (finiteOpen c) le_rfl (finiteCoordinate c) :=
  (Classical.choose_spec (exists_section c (finiteCoordinate c) 1 (one_compatible c))).1
lemma one_infinity : (M c).presheaf.map (homOfLE (show infinityOpen c ≤ ⊤ from le_top)).op (one c) =
    infinity c (infinityOpen c) le_rfl 1 :=
  (Classical.choose_spec (exists_section c (finiteCoordinate c) 1 (one_compatible c))).2

/-- The two actual global sections generate on the complete two-open cover,
with bijective original coefficient maps on EVERY ambient subopen. -/
lemma zero_bijective (V : (X c).Opens) (hV : V ≤ finiteOpen c) :
    Function.Bijective (SectionGeneratedGluing318.genLinear (ModuleGlobalSections318.ofTop (M c) (zero c)) V) :=
  OriginalGlobalFrameGenerator318.bijective (M c) (finiteOpen c) (finiteFrame c 1).symm
    (zero c) (zero_finite c) V hV
lemma one_bijective (V : (X c).Opens) (hV : V ≤ infinityOpen c) :
    Function.Bijective (SectionGeneratedGluing318.genLinear (ModuleGlobalSections318.ofTop (M c) (one c)) V) :=
  OriginalGlobalFrameGenerator318.bijective (M c) (infinityOpen c) (infinityFrame c 1).symm
    (one c) (one_infinity c) V hV
end ContactOriginalPositiveGlobalSections318
