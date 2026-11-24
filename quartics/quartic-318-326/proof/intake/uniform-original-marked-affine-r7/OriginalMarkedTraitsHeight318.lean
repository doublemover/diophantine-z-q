module
public import OriginalMarkedChartSpecialization318
public section
noncomputable section
namespace OriginalMarkedTraitsHeight318
open NumberField OriginalMarkedTraitInverse318 OriginalKleinPrimitivePair318
open OriginalGlobalHodgeIdealHeight318 SelectedSameADirectBicanonicalHeight318
open OriginalTwoMarkedTensorsR8_318
open scoped TensorProduct nonZeroDivisors
variable {E H2 D2 : Type*} [Field E] [NumberField E] [AddCommGroup H2] [Module E H2]
    [AddCommGroup D2] [Module E D2]

/-- Vector-level physical raw KS in the single marked cotangent coframe. -/
def rawRead {S M : Type*} [CommRing S] [Algebra S E] [AddCommGroup M] [Module S M]
    (f:M→ₗ[S]E) (η:H2≃ₗ[E]E) (dt:D2≃ₗ[E]E) (ψ:H2≃ₗ[E]D2) : M⊗[S]M →ₗ[S]E :=
  dt (ψ (η.symm 1)) • square f

omit [NumberField E] in
theorem reading {S M : Type*} [CommRing S] [Algebra S E] [AddCommGroup M] [Module S M]
    (f:M→ₗ[S]E) (η:H2≃ₗ[E]E) (dt:D2≃ₗ[E]E) (ψ:H2≃ₗ[E]D2) (h:M⊗[S]M) :
    rawRead f η dt ψ h=dt (ψ (η.symm (square f h))) := by
  have hx : η.symm (square f h)=square f h • η.symm 1 := by rw [←map_smul,smul_eq_mul,mul_one]
  rw [hx,map_smul,map_smul,smul_eq_mul,rawRead,LinearMap.smul_apply,smul_eq_mul,mul_comm]

/-- End-to-end finite half to the exact R8 strict bound: take R5-type
physical charts constructed independently at each closed point of the
two genuine proper marks. Produce both preimages in the *actual*
open Hodge tensor modules, the common nonprincipal lattice and height.
No global number-ring affine trivialization is a premise. -/
theorem height
    (S3 S11 C : Type*) [CommRing S3] [CommRing S11] [CommRing C]
    [Algebra (𝓞 E) S3] [Algebra (𝓞 E) S11] [Algebra (𝓞 E) C]
    [Algebra S3 E] [Algebra S11 E] [Algebra C E] [Algebra S3 C] [Algebra S11 C]
    [IsScalarTower (𝓞 E) S3 E] [IsScalarTower (𝓞 E) S11 E] [IsScalarTower (𝓞 E) C E]
    [IsScalarTower S3 C E] [IsScalarTower S11 C E]
    [IsLocalization.Away (3:𝓞 E) S3] [IsLocalization.Away (11:𝓞 E) S11]
    [IsLocalization.Away (33:𝓞 E) C]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module S3 M] [Module S11 N]
    [Module.Finite S3 M] [Module.Finite S11 N] (f : M→ₗ[S3]E) (g : N→ₗ[S11]E)
    (nz : ∃m,f m≠0) (mark : C⊗[S3]M ≃ₗ[C] C⊗[S11]N)
    (wedge : (OriginalHodgeModuleOverlap318.read (C:=C) g).comp mark.toLinearMap=
      OriginalHodgeModuleOverlap318.read f) 
    (η : H2≃ₗ[E]E) (dt : D2≃ₗ[E]E) (ψ : H2≃ₗ[E]D2)
    (q:ℚ) (nP:P (q:E)≠0)
    (g3 : ∀m:Ideal S3,∀hm:m.IsMaximal,letI : m.IsPrime := hm.isPrime
      Nonempty (Chart (rawRead f η dt ψ) (fun i => coefficients (F:=E) q i / P (q:E)) m))
    (g11 : ∀m:Ideal S11,∀hm:m.IsMaximal,letI : m.IsPrime := hm.isPrime
      Nonempty (Chart (rawRead g η dt ψ) (fun i => coefficients (F:=E) q i / P (q:E)) m))
    (arch : InfinitePlace E→ℝ) (pos : ∀w,0<arch w)
    (period : ∀w : InfinitePlace E,∃ U h : ℝ,2*max 32 (w (q:E))≤U ∧ 64≤h ∧
      w.val ((P (q:E)*dt (ψ (η.symm 1)))⁻¹)*(arch w)^2=4/(U*h)) :
    ∃ (I : FractionalIdeal (𝓞 E)⁰ E) (hn : I≠0),
      (I:Submodule (𝓞 E) E)=f.range.restrictScalars (𝓞 E) ⊓ g.range.restrictScalars (𝓞 E) ∧
      Height.logHeight₁ (q/32)<2*(idealFrame I hn arch pos).normalizedDegree+11 := by
  let y (i:Fin 2) := dt.symm (coefficients (F:=E) q i / P (q:E))
  obtain ⟨a,ha⟩ := assemble (rawRead f η dt ψ) _ g3
  obtain ⟨b,hb⟩ := assemble (rawRead g η dt ψ) _ g11
  apply OriginalTwoMarkedTensorsR8_318.height S3 S11 C f g nz mark wedge a b η dt ψ y
    (q:=q) (P:=P (q:E)) (nP:=nP) (arch:=arch) (pos:=pos) (period:=period)
  · intro i; apply dt.injective
    simpa only [←reading,map_smul,smul_eq_mul,y,LinearEquiv.apply_symm_apply] using ha i
  · intro i; apply dt.injective
    simpa only [←reading,map_smul,smul_eq_mul,y,LinearEquiv.apply_symm_apply] using hb i
  · intro i; simp only [y,LinearEquiv.apply_symm_apply]; field_simp
end OriginalMarkedTraitsHeight318
