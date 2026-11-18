module
public import OriginalBranchCotangentFiber318
public section
noncomputable section
namespace OriginalBicanonicalRationalValues318
open Polynomial ContactBicanonicalCoefficients318
open SourceDenominatorCover318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ i,RationalContactPoint318.parameters c t i≠0) (i : Fin 4)
abbrev K := RationalContactPoint318.PointField c t
@[expose] def D : ℚ := Polynomial.aeval t (untwisted i)

/-- Three other contacts, with no extension-field coordinates. -/
theorem D_product : D t i=∏ j : Fin 3,(t-LinearContactSquareclass318.contacts
    (FourRootPivot318.indices i j.succ)) := by
  simp only [D,untwisted,map_prod,map_sub,aeval_X,aeval_C]

include hn in
theorem D_ne : D t i≠0 := by
  rw [D_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  intro h
  apply hn (FourRootPivot318.indices i j.succ)
  rw [RationalContactPoint318.parameters_eq,h,mul_zero]

@[expose] def scalar0 : ℚ :=
  (VerticalSection318.J:ℚ)^2 * 4 / ((c i:ℚ)*D t i)

/-- The branch coefficient before evaluating is an asserted inverse in an
actual localization. After multiplying by its actual denominator, its value
in the same original fiber agrees with the rational numerator. -/
theorem coefficient_clear :
    ContactBranchPoint318.branchPoint c t hn i (branchQ0 c i) *
      ((Polynomial.aeval t (twisted c i) : ℚ) : K c t) =
      ((branchScale c i : ℚ) : K c t) := by
  let f := ContactBranchPoint318.branchPoint c t hn i
  let d := denominator c i
  have hd : f (algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i) d) =
      ((Polynomial.aeval t (twisted c i) : ℚ) : K c t) := by
    unfold d denominator
    rw [ContactBranchPoint318.branchPoint_polynomial] <;> exact map_ratCast _ _
  have hraw : branchQ0 c i *
      algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i) d =
      algebraMap ℚ (BranchRing c i) (branchScale c i : ℚ) := by
    unfold branchQ0 d
    rw [mul_assoc,mul_comm (IsLocalization.Away.invSelf _),IsLocalization.Away.mul_invSelf,mul_one]
  have h := congrArg f hraw
  rw [map_mul,hd] at h
  change f (branchQ0 c i) * _ = _
  simpa [f,map_ratCast] using h

theorem eval_twisted :
    Polynomial.aeval t (twisted c i)=(twistUnit c i:ℚ)*D t i := by
  rw [twisted_factor,map_mul,aeval_C] <;> rfl

include hn in
theorem scalar_identity :
    (VerticalSection318.J:ℚ)^2 * (branchScale c i:ℚ) /
      Polynomial.aeval t (twisted c i) = scalar0 c t i := by
  rw [eval_twisted]
  unfold scalar0 branchScale
  simp only [Units.val_mul,Units.val_inv_eq_inv_val]
  change (VerticalSection318.J:ℚ)^2 * (4*(twistUnit c i:ℚ)*(c i:ℚ)⁻¹) /
    ((twistUnit c i:ℚ)*D t i) = (VerticalSection318.J:ℚ)^2*4 / ((c i:ℚ)*D t i)
  field_simp [(twistUnit c i).ne_zero,(c i).ne_zero,D_ne c t hn i] <;> ring

theorem a0_literal :
    ContactBicanonicalPointHeight318.a0 c t hn i = (scalar0 c t i : K c t) := by
  have he : Polynomial.aeval t (twisted c i)≠0 := by
    rw [eval_twisted]
    exact mul_ne_zero (twistUnit c i).ne_zero (D_ne c t hn i)
  have hd : ((Polynomial.aeval t (twisted c i):ℚ):K c t) ≠ 0 := by exact_mod_cast he
  have hf := (eq_div_iff hd).mpr (coefficient_clear c t hn i)
  rw [OriginalBranchCotangentFiber318.original_value_zero,hf,←scalar_identity c t hn i]
  push_cast
  ring

theorem a1_literal : ContactBicanonicalPointHeight318.a1 c t hn i =
    ((t*scalar0 c t i : ℚ):K c t) := by
  rw [ContactBicanonicalPointHeight318.ratio,a0_literal,Rat.cast_mul]
end OriginalBicanonicalRationalValues318
