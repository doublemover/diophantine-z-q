module
public import ActualGaussianWeberNamedLocalInclusion318
public import Mathlib.RingTheory.Localization.Basic
public section
noncomputable section

namespace ActualGaussianWeberOldIntegralValueContraction318

open NumberField IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberActualLocalizedFrob318
open ActualGaussianWeberNamedLocalInclusion318

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L]
variable (W : IntermediateField Base L) [NumberField W]
variable (v : HeightOneSpectrum (𝓞 W)) (w : HeightOneSpectrum (𝓞 L))

/-- Integrality of a value already in the old field descends along
its exact named place. Neither field is replaced by an isomorphic
copy and no absolute Galois or unramifiedness premise is needed. -/
theorem old_value_locally_integral_of_upper
    (hwv : SameContraction L W v w) (z : W)
    (hzB : algebraMap W L z ∈ AtPlace L w) :
    ∃ a : OldLocal L W v, oldLocalToField L W v a=z := by
  let A := OldLocal L W v
  let C := AtPlace W v
  let B := AtPlace L w
  let e : A ≃ₐ[𝓞 W] C := IsLocalization.algEquiv v.asIdeal.primeCompl A C
  have he : C.subtype.comp e.toRingHom=oldLocalToField L W v := by
    apply IsLocalization.ringHom_ext v.asIdeal.primeCompl
    apply RingHom.ext
    intro x
    change C.subtype (e (algebraMap (𝓞 W) A x))=
      oldLocalToField L W v (algebraMap (𝓞 W) A x)
    rw [e.commutes,oldLocalToField_integral]
    change algebraMap C W (algebraMap (𝓞 W) C x)=algebraMap (𝓞 W) W x
    exact (IsScalarTower.algebraMap_apply (𝓞 W) C W x).symm
  have heval (a : A) : C.subtype (e a)=oldLocalToField L W v a :=
    DFunLike.congr_fun he a
  by_cases hzC : z∈C
  · let x : C := ⟨z,hzC⟩
    refine ⟨e.symm x,?_⟩
    calc
      _ = C.subtype (e (e.symm x)) := (heval (e.symm x)).symm
      _ = z := by rw [e.apply_symm_apply] <;> rfl
  · exfalso
    have hz : z≠0 := fun h => hzC (h ▸ C.zero_mem)
    let b : B := ⟨algebraMap W L z,hzB⟩
    let c : C := ⟨z⁻¹,(C.mem_or_inv_mem z).resolve_left hzC⟩
    let a : A := e.symm c
    have ha : oldLocalToField L W v a=z⁻¹ := by
      calc
        _ = C.subtype (e (e.symm c)) := (heval (e.symm c)).symm
        _ = z⁻¹ := by rw [e.apply_symm_apply] <;> rfl
    have haU : ¬IsUnit a := by
      rintro ⟨u,hu⟩
      let d : A := (↑(u⁻¹) : A)
      have hUnit : a*d=1 := by
        change a*(↑(u⁻¹) : A)=1
        rw [←hu]
        exact u.mul_inv
      have hProd : z⁻¹ * oldLocalToField L W v d=1 := by
        have h := congrArg (oldLocalToField L W v) hUnit
        simpa only [map_mul,map_one,ha] using h
      have hd : oldLocalToField L W v d=z := by
        apply mul_left_cancel₀ (inv_ne_zero hz)
        exact hProd.trans (inv_mul_cancel₀ hz).symm
      have hx : C.subtype (e d)=z := (heval d).trans hd
      have hmem : C.subtype (e d)∈C := (e d).property
      rw [hx] at hmem
      exact hzC hmem
    have hr : residue A a=0 := by
      by_contra h
      exact haU ((residue_ne_zero_iff_isUnit a).mp h)
    have hOld : oldLocalResidue L W v a=0 := by
      change (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal A).symm (residue A a)=0
      rw [hr,map_zero]
    let f := actualLocalInclusion L W v w hwv
    have hUpper : residue B (f a)=0 := by
      calc
        _ = oldQuotientIntoActualResidue L W v w hwv (oldLocalResidue L W v a) :=
          DFunLike.congr_fun (actualLocalInclusion_residue_square L W v w hwv) a
        _ = 0 := by rw [hOld,map_zero]
    have hField : B.subtype (f a)=algebraMap W L (oldLocalToField L W v a) :=
      DFunLike.congr_fun (actualLocalInclusion_field_triangle L W v w hwv) a
    have hProd : f a*b=1 := by
      apply B.subtype.injective
      rw [map_mul,map_one,hField,ha]
      change algebraMap W L (z⁻¹)*algebraMap W L z=1
      rw [←map_mul,inv_mul_cancel₀ hz,map_one]
    have h := congrArg (residue B) hProd
    rw [map_mul,hUpper,zero_mul,map_one] at h
    exact zero_ne_one h

/-- Thus an old integral value has p-fixed reduction at the actual
upper place whenever the old quotient has p-fixed residues. -/
theorem upper_residue_pow_fixed_of_old_value
    (hwv : SameContraction L W v w) (p : ℕ)
    (hSplit : ∀ r : (𝓞 W) ⧸ v.asIdeal, r^p=r)
    (z : W) (x : AtPlace L w) (hx : (AtPlace L w).subtype x=algebraMap W L z) :
    (residue (AtPlace L w) x)^p=residue (AtPlace L w) x := by
  let B := AtPlace L w
  have hzB : (AtPlace L w).subtype x∈B := x.property
  rw [hx] at hzB
  obtain ⟨a,ha⟩ := old_value_locally_integral_of_upper L W v w hwv z hzB
  let f := actualLocalInclusion L W v w hwv
  let e := oldQuotientIntoActualResidue L W v w hwv
  have hfx : f a=x := by
    apply B.subtype.injective
    calc
      _ = algebraMap W L (oldLocalToField L W v a) :=
        DFunLike.congr_fun (actualLocalInclusion_field_triangle L W v w hwv) a
      _ = B.subtype x := (congrArg (algebraMap W L) ha).trans hx.symm
  have hEq : residue B x=e (oldLocalResidue L W v a) :=
    (congrArg (residue B) hfx.symm).trans
      (DFunLike.congr_fun (actualLocalInclusion_residue_square L W v w hwv) a)
  rw [hEq,←map_pow,hSplit]

end ActualGaussianWeberOldIntegralValueContraction318
