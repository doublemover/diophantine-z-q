module
public import PELMaximalHalfOctagonSphere318
public section
noncomputable section
namespace PELMaximalHalfOctagonCoordinates318
open Set
open PELMaximalHalfOctagonShape318 ReflectedDiskJoukowski318

/-- The uncentered literal upper half of the octagon in the ORIGINAL scaled
real coordinates. No arithmetic quotient has been replaced by this set. -/
@[expose] def upperCut : Set (ℝ × ℝ) := {P |
  0≤P.2 ∧ P.2≤1 ∧ -30≤P.1 ∧ P.1≤30 ∧
  P.1+7*P.2≤35 ∧ -P.1+7*P.2≤35}

@[expose] def centerHomeomorph : (ℝ × ℝ) ≃ₜ ℂ where
  toFun P := (P.1:ℂ)+((P.2-1/2:ℝ):ℂ)*Complex.I
  invFun z := (z.re,z.im+1/2)
  left_inv P := by ext <;> simp <;> ring
  right_inv z := by apply Complex.ext <;> simp <;> ring
  continuous_toFun :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp (continuous_snd.sub continuous_const)).mul continuous_const)
  continuous_invFun := Complex.continuous_re.prodMk (Complex.continuous_im.add continuous_const)

theorem centered_membership (P : ℝ × ℝ) : P∈upperCut ↔ centerHomeomorph P∈centeredPolygon := by
  change P∈upperCut ↔ (P.1+(P.2-1/2:ℝ)*Complex.I:ℂ)∈centeredPolygon
  simp only [upperCut,centeredPolygon,Set.mem_setOf_eq,centerHomeomorph,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,mul_one,zero_add]
  constructor <;> rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem center_reflection (P : ℝ × ℝ) :
    centerHomeomorph (-P.1,P.2)=reflected (centerHomeomorph P) := by
  apply Complex.ext <;> simp [centerHomeomorph,reflected] <;> ring

@[expose] def upperCutCenter : upperCut ≃ₜ centeredPolygon :=
  centerHomeomorph.subtype centered_membership

@[expose] def upperCutDisk : upperCut ≃ₜ Disk :=
  upperCutCenter.trans polygonDiskHomeomorph

theorem upperCut_reflection (P : ℝ × ℝ) : (-P.1,P.2)∈upperCut ↔ P∈upperCut := by
  simp only [upperCut,Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem disk_reflection (P : upperCut) :
    (upperCutDisk ⟨(-P.val.1,P.val.2),(upperCut_reflection P.val).mpr P.property⟩).val=
      reflected (upperCutDisk P).val := by
  have h : upperCutCenter ⟨(-P.val.1,P.val.2),(upperCut_reflection P.val).mpr P.property⟩=
      ⟨reflected (upperCutCenter P).val,(polygon_reflected _).mpr (upperCutCenter P).property⟩ := by
    apply Subtype.ext
    exact center_reflection P.val
  change (polygonDiskHomeomorph (upperCutCenter _)).val=reflected (polygonDiskHomeomorph (upperCutCenter P)).val
  rw [h]
  exact normalized_reflection (upperCutCenter P)
end PELMaximalHalfOctagonCoordinates318
