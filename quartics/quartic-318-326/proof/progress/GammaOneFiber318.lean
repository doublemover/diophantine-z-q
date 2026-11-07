module
public import GammaOneFree318
public import PeterssonQuotient318
public section
noncomputable section
open UpperHalfPlane DerivativeCocycle318 QuadraticFiber318 PeterssonQuotient318
open scoped MatrixGroups
namespace GammaOneFiber318
set_option maxHeartbeats 0

@[expose] def positiveMatrix (N:ℕ) : CongruenceSubgroup.Gamma1 N →* G :=
  (Matrix.SpecialLinearGroup.toGLPos.comp (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℝ))).comp
    (CongruenceSubgroup.Gamma1 N).subtype

@[expose] def image (N:ℕ) : Subgroup G := (positiveMatrix N).range

theorem image_fixed_eq_one (N:ℕ) (hN:5≤N) (g:G) (hg:g∈image N) (z:UpperHalfPlane)
    (hz:g•z=z) : g=1 := by
  obtain ⟨gamma,rfl⟩:=hg
  have hz' : GammaOneFree318.realMatrix gamma.val•z=z := hz
  have he := (GammaOneFree318.subgroup_fixed_iff N hN gamma z).mp hz'
  rw [he,map_one]

/-- Actual coefficients at a fixed lift map to the genuine quotient fiber. -/
@[expose] def fiberParam (H:Subgroup G) (z:UpperHalfPlane) (q:ℂ) :
    {v:Total H // projection H v=(⟦z⟧:Base H)} := ⟨⟦Fiber.mk z q⟧,rfl⟩

theorem fiberParam_injective (H:Subgroup G) (z:UpperHalfPlane)
    (hf:∀g:G,g∈H→g•z=z→g=1) : Function.Injective (fiberParam H z) := by
  intro q r he
  have hq : (⟦Fiber.mk z q⟧:Total H)=⟦Fiber.mk z r⟧ := congrArg Subtype.val he
  obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp (Quotient.exact hq)
  change (g:G) • Fiber.mk z r=Fiber.mk z q at hg
  have hp := congrArg Fiber.point hg
  have h1 : (g:G)=1 := hf g g.property hp
  rw [h1,one_smul] at hg
  exact (congrArg Fiber.value hg).symm

/-- Every actual orbit-quotient fiber is represented over each chosen base lift. -/
theorem fiberParam_surjective (H:Subgroup G) (z:UpperHalfPlane) :
    Function.Surjective (fiberParam H z) := by
  rintro ⟨v,hv⟩
  induction v using Quotient.inductionOn with
  | h v =>
    change (⟦v.point⟧:Base H)=⟦z⟧ at hv
    obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp (Quotient.exact hv)
    change (g:G) • z=v.point at hg
    let w:Fiber := (g:G)⁻¹ • v
    have hw:w.point=z := by
      change (g:G)⁻¹ • v.point=z
      rw [←hg,inv_smul_smul]
    refine ⟨w.value,?_⟩
    apply Subtype.ext
    change (⟦Fiber.mk z w.value⟧:Total H)=⟦v⟧
    have he: Fiber.mk z w.value=w := by apply Fiber.ext <;> simp [hw]
    rw [he]
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact ⟨g⁻¹,rfl⟩

/-- At fine level N>=5, each genuine Petersson orbit fiber has a unique complex coefficient
relative to a chosen lift. No quotient atlas or local-triviality premise is used. -/
@[expose] def coefficientEquiv (N:ℕ) (hN:5≤N) (z:UpperHalfPlane) :
    ℂ ≃ {v:Total (image N) // projection (image N) v=(⟦z⟧:Base (image N))} :=
  Equiv.ofBijective (fiberParam (image N) z)
    ⟨fiberParam_injective _ _ (image_fixed_eq_one N hN · · z),fiberParam_surjective _ _⟩

theorem coefficientEquiv_norm (N:ℕ) (hN:5≤N) (z:UpperHalfPlane) (q:ℂ) :
    PeterssonQuotient318.norm (image N) (coefficientEquiv N hN z q).val=
      PeterssonSectionNorm318.quadraticNorm (PoincareCurvature318.coefficient z) q := rfl
end GammaOneFiber318
