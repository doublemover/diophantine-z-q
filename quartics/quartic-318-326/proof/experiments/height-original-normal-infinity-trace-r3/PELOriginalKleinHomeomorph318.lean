module
public import PELDirichletOrbitBound318
public section
noncomputable section
namespace PELOriginalKleinHomeomorph318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
set_option maxHeartbeats 1800000
abbrev Disk := {p : ℝ×ℝ // p.1^2+p.2^2<1}

/-- The auxiliary coordinates are the REAL Klein disk coordinates. This
homeomorphism is not asserted to be holomorphic. -/
theorem disk_identity (τ : HalfPlane) :
    (1-(firstDisk τ)^2-(secondDisk τ)^2)*(Complex.normSq (τ:ℂ)+1)^2=
      4*(τ:ℂ).im^2 := by
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  unfold firstDisk secondDisk
  field_simp [hn] <;> simp only [Complex.normSq_apply] <;> ring

theorem disk_mem (τ : HalfPlane) : (firstDisk τ)^2+(secondDisk τ)^2<1 := by
  have h := disk_identity τ
  have hy : 0<(τ:ℂ).im^2 := sq_pos_of_pos τ.property
  by_contra hn
  have hmul := mul_nonpos_of_nonpos_of_nonneg (by linarith :
    1-(firstDisk τ)^2-(secondDisk τ)^2≤0) (sq_nonneg (Complex.normSq (τ:ℂ)+1))
  nlinarith

@[expose] def toDisk (τ : HalfPlane) : Disk :=
  ⟨(firstDisk τ,secondDisk τ),disk_mem τ⟩

theorem second_lt_one (p : Disk) : p.val.2<1 := by
  have hp := p.property
  nlinarith [sq_nonneg p.val.1,sq_nonneg (p.val.2-1)]

@[expose] def fromDisk (p : Disk) : HalfPlane :=
  ⟨((p.val.1/(1-p.val.2):ℝ):ℂ)+
    ((Real.sqrt (1-p.val.1^2-p.val.2^2)/(1-p.val.2):ℝ):ℂ)*Complex.I,by
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_im,
        Complex.I_re,Complex.ofReal_re,mul_one,mul_zero,add_zero,zero_add]
      exact div_pos (Real.sqrt_pos.mpr (by linarith [p.property]))
        (sub_pos.mpr (second_lt_one p))⟩

theorem fromDisk_re (p : Disk) : (fromDisk p:ℂ).re=p.val.1/(1-p.val.2) := by
  simp [fromDisk]
theorem fromDisk_im (p : Disk) : (fromDisk p:ℂ).im=
    Real.sqrt (1-p.val.1^2-p.val.2^2)/(1-p.val.2) := by
  simp [fromDisk]

theorem fromDisk_norm (p : Disk) :
    Complex.normSq (fromDisk p:ℂ)+1=2/(1-p.val.2) := by
  have hd : 1-p.val.2≠0 := (sub_pos.mpr (second_lt_one p)).ne'
  have hs := Real.sq_sqrt (show 0≤1-p.val.1^2-p.val.2^2 by linarith [p.property])
  rw [Complex.normSq_apply,fromDisk_re,fromDisk_im]
  field_simp [hd]
  nlinarith

theorem to_from (p : Disk) : toDisk (fromDisk p)=p := by
  apply Subtype.ext
  apply Prod.ext
  · change firstDisk (fromDisk p)=p.val.1
    unfold firstDisk
    rw [fromDisk_norm,fromDisk_re]
    field_simp [(sub_pos.mpr (second_lt_one p)).ne'] <;> ring
  · change secondDisk (fromDisk p)=p.val.2
    unfold secondDisk
    have hn := fromDisk_norm p
    have hd : 1-p.val.2≠0 := (sub_pos.mpr (second_lt_one p)).ne'
    have hh : Complex.normSq (fromDisk p:ℂ)-1=2/(1-p.val.2)-2 := by linarith
    rw [hn,hh]
    field_simp [hd] <;> ring

theorem toDisk_injective : Function.Injective toDisk := by
  intro τ σ h
  have h1 : firstDisk τ=firstDisk σ := congrArg (fun p : Disk => p.val.1) h
  have h2 : secondDisk τ=secondDisk σ := congrArg (fun p : Disk => p.val.2) h
  have hnτ : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hnσ : Complex.normSq (σ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (σ:ℂ)]
  have hn : Complex.normSq (τ:ℂ)=Complex.normSq (σ:ℂ) := by
    unfold secondDisk at h2
    field_simp [hnτ,hnσ] at h2
    nlinarith
  have hr : (τ:ℂ).re=(σ:ℂ).re := by
    unfold firstDisk at h1
    rw [hn] at h1
    have ht := congrArg (fun z : ℝ => z*(Complex.normSq (σ:ℂ)+1)) h1
    simp only [div_mul_cancel₀ _ hnσ] at ht
    linarith
  have hi : (τ:ℂ).im=(σ:ℂ).im := by
    rw [Complex.normSq_apply,Complex.normSq_apply,hr] at hn
    nlinarith [τ.property,σ.property]
  exact Subtype.ext (Complex.ext hr hi)

theorem continuous_toDisk : Continuous toDisk := by
  apply Continuous.subtype_mk
  have hn (τ : HalfPlane) : Complex.normSq (τ:ℂ)+1≠0 := by
    nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hN : Continuous (fun τ : HalfPlane => Complex.normSq (τ:ℂ)+1) :=
    (PELHeightCompactSublevels318.normSq_continuous.comp continuous_subtype_val).add continuous_const
  exact ((continuous_const.mul (Complex.continuous_re.comp continuous_subtype_val)).div hN hn).prodMk
    (((PELHeightCompactSublevels318.normSq_continuous.comp continuous_subtype_val).sub continuous_const).div hN hn)

theorem continuous_fromDisk : Continuous fromDisk := by
  apply Continuous.subtype_mk
  have hu : Continuous (fun p : Disk => p.val.1) := continuous_fst.comp continuous_subtype_val
  have hv : Continuous (fun p : Disk => p.val.2) := continuous_snd.comp continuous_subtype_val
  have hd := continuous_const.sub hv
  have hx := hu.div hd (fun p => (sub_pos.mpr (second_lt_one p)).ne')
  have hy := (Real.continuous_sqrt.comp ((continuous_const.sub (hu.pow 2)).sub (hv.pow 2))).div hd
    (fun p => (sub_pos.mpr (second_lt_one p)).ne')
  exact (Complex.continuous_ofReal.comp hx).add
    ((Complex.continuous_ofReal.comp hy).mul continuous_const)

@[expose] def originalHomeomorph : HalfPlane ≃ₜ Disk where
  toFun := toDisk
  invFun := fromDisk
  left_inv τ := toDisk_injective (to_from (toDisk τ))
  right_inv := to_from
  continuous_toFun := continuous_toDisk
  continuous_invFun := continuous_fromDisk
end PELOriginalKleinHomeomorph318
