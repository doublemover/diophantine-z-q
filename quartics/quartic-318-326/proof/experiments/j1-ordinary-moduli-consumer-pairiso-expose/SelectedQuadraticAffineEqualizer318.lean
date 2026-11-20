module
public import EvenContactEtale318
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public section
noncomputable section
open scoped TensorProduct
open EvenContactEtale318

namespace SelectedQuadraticAffineEqualizer318
variable {R : Type*} [CommRing R] (c : Rˣ)
local notation "U" => RootRing c
local notation "U₂" => U ⊗[R] U

abbrev left : U →ₐ[R] U₂ := Algebra.TensorProduct.includeLeft
abbrev right : U →ₐ[R] U₂ := Algebra.TensorProduct.includeRight

theorem scalar_equalizes (r : R) :
    left c (algebraMap R U r) = right c (algebraMap R U r) := by
  exact ((left c).commutes r).trans ((right c).commutes r).symm

variable [Nontrivial R]

/-- Exact equalizer of the two actual Cech maps of this root cover.
Faithful flatness is the proved property of the chosen root ring. -/
theorem equalizes_iff_scalar (z : U) :
    left c z = right c z ↔ ∃ r : R, algebraMap R U r = z := by
  constructor
  · intro h
    letI : Module.FaithfullyFlat R U := rootRing_faithfullyFlat c
    let L := LinearMap.range (Algebra.linearMap R U)
    have h1 : (1:U) ∈ L := ⟨1,by simp⟩
    have hk : (1:U) ∈ LinearMap.ker L.mkQ := by rwa [Submodule.ker_mkQ]
    have hq : L.mkQ (1:U) = 0 := hk
    have ht := congrArg (L.mkQ.lTensor U) h
    change (L.mkQ.lTensor U) (z ⊗ₜ[R] (1:U)) =
      (L.mkQ.lTensor U) ((1:U) ⊗ₜ[R] z) at ht
    have hz : ((1:U) ⊗ₜ[R] L.mkQ z) = 0 := by
      simpa only [LinearMap.lTensor_tmul,hq,TensorProduct.tmul_zero] using ht.symm
    have hz' : z ∈ LinearMap.ker L.mkQ :=
      (Module.FaithfullyFlat.one_tmul_eq_zero_iff (A := U) (L.mkQ z)).mp hz
    rw [Submodule.ker_mkQ] at hz'
    exact hz'
  · rintro ⟨r,rfl⟩
    exact scalar_equalizes c r

theorem scalar_injective : Function.Injective (algebraMap R U) := by
  letI : Module.FaithfullyFlat R U := rootRing_faithfullyFlat c
  exact FaithfulSMul.algebraMap_injective R U

section Factor
variable {D : Type*} [CommRing D] [Algebra R D]

/-- Unique affine descent of a map to the actual cover, given equality
on its two actual overlap maps. -/
theorem factor_unique (f : D →ₐ[R] U)
    (hf : (left c).comp f = (right c).comp f) :
    ∃! g : D →ₐ[R] R, (Algebra.ofId R U).comp g = f := by
  let i := Algebra.ofId R U
  have hi : Function.Injective i := scalar_injective c
  let E := AlgEquiv.ofInjective i hi
  have hr (z : D) : f z ∈ i.range := by
    obtain ⟨r,hr⟩ := (equalizes_iff_scalar c (f z)).mp (DFunLike.congr_fun hf z)
    exact ⟨r,hr⟩
  let g := E.symm.toAlgHom.comp (f.codRestrict i.range hr)
  have hg : i.comp g = f := by
    apply AlgHom.ext
    intro z
    exact congrArg Subtype.val (E.apply_symm_apply (f.codRestrict i.range hr z))
  refine ⟨g,hg,?_⟩
  intro g' hg'
  apply AlgHom.ext
  intro z
  apply hi
  exact (DFunLike.congr_fun hg' z).trans (DFunLike.congr_fun hg z).symm

end Factor
end SelectedQuadraticAffineEqualizer318

#print axioms SelectedQuadraticAffineEqualizer318.equalizes_iff_scalar
#print axioms SelectedQuadraticAffineEqualizer318.factor_unique
