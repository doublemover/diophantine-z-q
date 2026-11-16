module
public import PELOriginalOrderedMatrixTransport318
public import PELOriginalCommonContactBase318
public import PELOriginalCompletedLegendreBijection318
public section
noncomputable section
namespace PELOriginalCommonCubicCoordinate318
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalManuscriptNormalization318
open PELOriginalGluedLegendreMap318 PELOriginalRegularCoverPatches318
open ComplexSphereFourPointNormalization318 ComplexSphereAffineNormalization318
open PELOriginalOrderedMatrixTransport318

@[expose] def offset : Fin 4→ℂ:=![1,0,0,0]
@[expose] def difference : Fin 4→ℂ:=![lambda-1,lambda,1,1]
lemma difference_ne (i:Fin 4) : difference i≠0:=by
  fin_cases i
  · exact sub_ne_zero.mpr lambda_ne_one
  · exact lambda_ne_zero
  · exact one_ne_zero
  · exact one_ne_zero

lemma normalization_finite (a b c t:ℂ)
    (h:Function.Injective (![∞,(a:ℂ),(b:ℂ),(c:ℂ)]:Fin 4→OnePoint ℂ)) :
    normalization ![∞,(a:ℂ),(b:ℂ),(c:ℂ)] h (t:OnePoint ℂ)=
      ((t-a)/(b-a):ℂ) := by
  change affineSphere _ _ _ (poleCoordinate ∞ (t:OnePoint ℂ))=_
  change affineSphere _ _ _ (t:OnePoint ℂ)=_
  rw [affineSphere_coe]
  simp only [ComplexSphereInfinityQuadruple318.finite_coordinate]
  congr 1
  ring

/-- The actual manuscript normalization has infinity first in every
ordered character. Its affine formula is DERIVED from that normalization. -/
lemma ordered_finite (i:Fin 4) (t:ℂ) :
    normalization (PELOriginalOrderedCharacterCoordinate318.points i)
      (PELOriginalOrderedCharacterCoordinate318.points_injective i) (t:OnePoint ℂ)=
      ((t-offset i)/difference i:ℂ) := by
  have hi:=PELOriginalOrderedCharacterCoordinate318.points_injective i
  rw [PELOriginalOrderedCharacterCoordinate318.literal_points] at hi ⊢
  fin_cases i <;> rw [normalization_finite] <;> simp [offset,difference]

lemma ordered_base (i:Fin 4) (x:CharacterBase i) (t:ℂ)
    (ht:coordinate (toMaximal i x)=(t:OnePoint ℂ)) :
    PELOriginalOrderedCharacterCoordinate318.normalizedMap i x=
      ((t-offset i)/difference i:ℂ) := by
  change normalization _ _ (coordinate (toMaximal i x))=_
  rw [ht,ordered_finite]

/-- Cubics on the common manuscript base in the exact omitted-character
order. The d^3 multiplier retains the original three finite roots. -/
lemma cubic_change (i:Fin 4) (t:ℂ) :
    difference i^3*ComplexLegendreMatrixTransport318.cubic
      (PELOriginalOrderedCharacterCoordinate318.parameter i) ((t-offset i)/difference i)=
      FourCharacterRootRecombination318.cubic PELOriginalCommonContactBase318.branches t i := by
  rw [PELOriginalOrderedCharacterCoordinate318.parameter_formula]
  have hλ:=lambda_ne_zero
  have hλ1:=sub_ne_zero.mpr lambda_ne_one
  fin_cases i <;>
    simp only [offset,difference,ComplexLegendreMatrixTransport318.cubic,
      PELOriginalCommonContactBase318.branches,FourCharacterRootRecombination318.cubic,
      FourCharacterRootRecombination318.triple,FourCharacterRootRecombination318.linear,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    field_simp [hλ,hλ1] <;> ring

@[expose] def scale (i:Fin 4) : ℂ:=
  (IsAlgClosed.exists_pow_nat_eq (difference i^3) (by decide : 0<2)).choose
lemma scale_square (i:Fin 4) : scale i^2=difference i^3:=
  (IsAlgClosed.exists_pow_nat_eq (difference i^3) (by decide : 0<2)).choose_spec
lemma scale_ne (i:Fin 4) : scale i≠0:=by
  intro h
  have hh:=scale_square i
  rw [h,zero_pow (by decide : 2≠0)] at hh
  exact pow_ne_zero 3 (difference_ne i) hh.symm

/-- Actual original y, transported through both marked coordinate changes.
Values outside the original regular locus are irrelevant, never declared
continuous. All consumers below retain their exact original source point. -/
@[expose] def ordinate (i:Fin 4) (x:CharacterBase i) : ℂ:=
  scale i*PELOriginalOrderedMatrixTransport318.ordinate i
    (coordinates i x).1 (coordinates i x).2

lemma actual_ordered_image (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i)
    (t:ℂ) (ht:coordinate (toMaximal i x)=(t:OnePoint ℂ)) :
    PELOriginalOrderedCharacterCoordinate318.oldToNew i
      ((coordinates i x).1:OnePoint ℂ)=((t-offset i)/difference i:ℂ) := by
  rw [coordinates_projection i x hx,
    PELOriginalOrderedCharacterCoordinate318.original_map_comparison]
  exact ordered_base i x t ht

/-- Genuine common-base cubic function, not an isomorphism chosen from j.
The SAME original x and SAME manuscript t occur on both sides. -/
theorem ordinate_square (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i)
    (t:ℂ) (ht:coordinate (toMaximal i x)=(t:OnePoint ℂ)) :
    ordinate i x^2=
      FourCharacterRootRecombination318.cubic PELOriginalCommonContactBase318.branches t i := by
  have hs:=(actual_finite_transport i (coordinates i x).1
    ((t-offset i)/difference i) (coordinates i x).2
    (actual_ordered_image i x hx t ht) (coordinates_equation i x hx)).2
  change (scale i*PELOriginalOrderedMatrixTransport318.ordinate i _ _)^2=_
  rw [mul_pow,scale_square,hs]
  exact cubic_change i t

/-- Nonzero multiplier on each actual finite fiber. This is what permits
recovery of the OLD y and hence of the actual original curve point. -/
lemma coefficient_ne (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i)
    (t:ℂ) (ht:coordinate (toMaximal i x)=(t:OnePoint ℂ)) :
    scale i*ordinateScale i/((matrixChange i).c*(coordinates i x).1+(matrixChange i).d)^2≠0 := by
  have hd:=((matrixChange i).finite_value _ _ (actual_ordered_image i x hx t ht)).1
  exact div_ne_zero (mul_ne_zero (scale_ne i) (ordinateScale_ne i)) (pow_ne_zero 2 hd)

lemma ordinate_formula (i:Fin 4) (x:CharacterBase i) : ordinate i x=
    (scale i*ordinateScale i/((matrixChange i).c*(coordinates i x).1+(matrixChange i).d)^2)*
      (coordinates i x).2 := by
  unfold ordinate PELOriginalOrderedMatrixTransport318.ordinate
  ring
end PELOriginalCommonCubicCoordinate318
