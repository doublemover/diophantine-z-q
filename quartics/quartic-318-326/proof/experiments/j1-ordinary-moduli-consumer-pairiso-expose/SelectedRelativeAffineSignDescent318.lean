module
public import SelectedFixedGeneratorGlue318
public section
noncomputable section
open Polynomial EvenContactEtale318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveRootSignDescent318
open SelectedFixedGeneratorGlue318
open scoped TensorProduct

namespace SelectedRelativeAffineSignDescent318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => Fixed n I τ
local notation "x₀" => generator n I τ hτ
variable (S : Type) [CommRing S] [Algebra R S] (c : Sˣ)
local notation "U" => RootRing c

abbrev rootUnit : Uˣ := (root_isUnit c).unit

theorem inverse_square : (↑((rootUnit S c)⁻¹):U)^2 = algebraMap S U (↑c⁻¹:S) := by
  have hr : (rootUnit S c)^2 = Units.map (algebraMap S U).toMonoidHom c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val,(root_isUnit c).unit_spec]
    exact root_square c
  have hi : ((rootUnit S c)⁻¹)^2 = Units.map (algebraMap S U).toMonoidHom c⁻¹ := by
    rw [inv_pow,hr,map_inv]
  simpa only [Units.val_pow_eq_pow_val] using congrArg (fun u : Uˣ => (u:U)) hi

/-- Normalize the actual abscissa by the unit square-ratio, over the
same coefficient ring, without choosing a sign or a square root in it. -/
abbrev normalized (x : S) : S := (↑c⁻¹:S)*x

variable (mark : Q →ₐ[R] U)
abbrev fixedMark : F →ₐ[R] U := mark.comp F.val
variable (x : S) (hx : mark (xbar n I) =
  (↑((rootUnit S c)⁻¹):U)^2 * algebraMap S U x)

include hτ hx in
private theorem scalar_value (z : F) :
    ∃ s : S, algebraMap S U s = fixedMark n I τ S c mark z := by
  have he : (fixedMark n I τ S c mark).comp (aeval x₀) =
      (IsScalarTower.toAlgHom R S U).comp (aeval (normalized S c x)) := by
    apply Polynomial.algHom_ext
    change mark (aeval x₀ X).val = algebraMap S U (aeval (normalized S c x) X)
    rw [aeval_X,aeval_X]
    change mark (xbar n I) = _
    rw [hx,inverse_square,map_mul]
  obtain ⟨p,hp⟩ := generated n I τ hτ z
  refine ⟨aeval (normalized S c x) p,?_⟩
  rw [←hp]
  exact (DFunLike.congr_fun he p).symm

include hτ hx in
theorem actual_branches :
    ((SelectedQuadraticAffineEqualizer318.left c).restrictScalars R).comp
        (fixedMark n I τ S c mark) =
      ((SelectedQuadraticAffineEqualizer318.right c).restrictScalars R).comp
        (fixedMark n I τ S c mark) := by
  apply AlgHom.ext
  intro z
  obtain ⟨s,hs⟩ := scalar_value n I τ hτ S c mark x hx z
  change SelectedQuadraticAffineEqualizer318.left c (fixedMark n I τ S c mark z) =
    SelectedQuadraticAffineEqualizer318.right c (fixedMark n I τ S c mark z)
  rw [←hs]
  exact SelectedQuadraticAffineEqualizer318.scalar_equalizes c s

include hτ hx in
/-- Effective descent over an arbitrary affine test algebra S of the
literal base. The evaluation keeps its R-algebra structure and descends
through the exact same Cech overlap over S. -/
theorem relative_descends [Nontrivial S] :
    ∃! f : F →ₐ[R] S,
      (IsScalarTower.toAlgHom R S U).comp f = fixedMark n I τ S c mark ∧
      f x₀ = normalized S c x := by
  let i := IsScalarTower.toAlgHom R S U
  have hi : Function.Injective i := SelectedQuadraticAffineEqualizer318.scalar_injective c
  let e := AlgEquiv.ofInjective i hi
  let p := fixedMark n I τ S c mark
  have hr (z : F) : p z ∈ i.range := by
    obtain ⟨s,hs⟩ := (SelectedQuadraticAffineEqualizer318.equalizes_iff_scalar c (p z)).mp
      (DFunLike.congr_fun (actual_branches n I τ hτ S c mark x hx) z)
    exact ⟨s,hs⟩
  let f := e.symm.toAlgHom.comp (p.codRestrict i.range hr)
  have hf : i.comp f = p := by
    apply AlgHom.ext
    intro z
    exact congrArg Subtype.val (e.apply_symm_apply (p.codRestrict i.range hr z))
  have hg : f x₀ = normalized S c x := by
    apply hi
    change (i.comp f) x₀ = _
    rw [hf]
    change mark (xbar n I) = algebraMap S U (normalized S c x)
    rw [hx,inverse_square,map_mul]
  refine ⟨f,⟨hf,hg⟩,?_⟩
  intro g hg'
  apply AlgHom.ext
  intro z
  apply hi
  exact (DFunLike.congr_fun hg'.1 z).trans (DFunLike.congr_fun hf z).symm

end SelectedRelativeAffineSignDescent318

#print axioms SelectedRelativeAffineSignDescent318.relative_descends
