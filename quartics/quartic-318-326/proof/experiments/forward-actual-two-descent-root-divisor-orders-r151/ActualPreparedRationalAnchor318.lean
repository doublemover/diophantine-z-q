module
public import ActualNormalizedAnchorLocalData318
public import AuxiliaryRationalAnchorOfLocals318
public section
noncomputable section
namespace ActualPreparedRationalAnchor318

/-- The specialized prepared target, not universal hglobal. The actual
parameter family supplies every finite local vector and coefficient
condition; the auxiliary-prime construction produces the rational point.
This source remains an uncompiled end-to-end candidate until all staged
dependencies and this theorem pass the strict hosted kernel checks. -/
theorem prepared_representation (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    let ns := FixedArithmeticLabels318.labels a A B
      (PreparedAnchorLabels318.multiplier N d) (PreparedAnchorLabels318.multiplier_ne N d hd)
    let r := ActualAnchorRatio318.ratio ns N
    ∃ x y z : ℚ, x^2+6*y^2-2*z^2=3*r^2-2 := by
  dsimp only
  let ns := FixedArithmeticLabels318.labels a A B
    (PreparedAnchorLabels318.multiplier N d) (PreparedAnchorLabels318.multiplier_ne N d hd)
  let r := ActualAnchorRatio318.ratio ns N
  obtain ⟨e,C,he0,hC0,hCsf,hC24,he,hsix,hloc⟩ :=
    ActualNormalizedAnchorLocalData318.prepared_normalized_local_data a A B N d hd
  have hlocal : ∀ p (hp : p∈insert 2 (insert 3 C.natAbs.primeFactors)),
      ∀ [Fact p.Prime], ∃ X Z T Y : ℚ_[p],
        ¬(X=0 ∧ Z=0 ∧ T=0 ∧ Y=0) ∧
        X^2-2*Z^2=(C:ℚ_[p])*T^2-6*Y^2 := by
    intro p hp inst
    exact hloc p
  have hrep := AuxiliaryRationalAnchorOfLocals318.rational_of_finite_local_data
    C hC24 hCsf hsix hlocal
  have hden : (r.den:ℚ)≠0 := by exact_mod_cast r.den_ne_zero
  have hclear : (r.den:ℚ)^2*(3*r^2-2)=((e^2*C:ℤ):ℚ) := by
    rw [he]
    calc
      (r.den:ℚ)^2*(3*r^2-2)=
          (r.den:ℚ)^2*(3*((r.num:ℚ)/(r.den:ℚ))^2-2) := by rw [Rat.num_div_den]
      _=((3*r.num^2-2*(r.den:ℤ)^2:ℤ):ℚ) := by
        push_cast
        field_simp [hden] <;> ring
  have hid : 3*r^2-2=((e:ℚ)/(r.den:ℚ))^2*(C:ℚ) := by
    push_cast at hclear
    field_simp [hden]
    nlinarith [hclear]
  exact AuxiliaryCombinedAnchor318.scaled_representation
    (C:ℚ) (3*r^2-2) ((e:ℚ)/(r.den:ℚ)) hid hrep

end ActualPreparedRationalAnchor318
