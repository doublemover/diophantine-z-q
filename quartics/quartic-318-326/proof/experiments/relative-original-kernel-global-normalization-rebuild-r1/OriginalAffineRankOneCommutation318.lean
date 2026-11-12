module
public import OriginalLineAffineModel318
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.LocalProperties.Submodule
public section
noncomputable section
namespace OriginalAffineRankOneCommutation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u

lemma in_frame {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    (e : M ≃ₗ[S] S) (φ : M →ₗ[S] S) (s x : M) : φ s • x=φ x • s := by
  have hφ (y : M) : φ y=e y * φ (e.symm 1) := by
    have hy : y=e y • e.symm 1 := by
      apply e.injective
      simp
    calc
      φ y=φ (e y • e.symm 1) := congrArg φ hy
      _ = e y * φ (e.symm 1) := by rw [map_smul, smul_eq_mul]
  apply e.injective
  simp only [map_smul, smul_eq_mul, hφ]
  ring

variable (A : CommRingCat.{u}) (L : Line (Spec A))
local notation "P" => OriginalLineAffineModel318.sections A L

/-- Actual rank-one commutation for EVERY original affine line, even
when the whole-chart module is nonfree. Localize at the original
principal frame cover and use its actual localization maps to descend. -/
lemma commutation (φ : Module.Dual A P) (s x : P) : φ s • x=φ x • s := by
  let T := AffineLineModule318.frameSet A L.object
  have hspan : Ideal.span T=⊤ := AffineLineModule318.span_top A L.object
    (AffineLineFrameCover318.principalCover A L.object L.opens L.cover L.frame)
  apply Module.eq_of_isLocalized_span T hspan
    (fun r : T => Γ(L.object, AffineLineModule318.basic A r.val))
    (fun r : T => AffineLineModule318.restriction A L.object r.val)
  intro r
  let C := Γ(Spec A, AffineLineModule318.basic A r.val)
  let ρ := AffineLineModule318.restriction A L.object r.val
  let a : A →ₗ[A] C := Algebra.linearMap A C
  let ψ : Γ(L.object, AffineLineModule318.basic A r.val) →ₗ[C] C :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers r.val) ρ a C φ
  have hψ (y : P) : ψ (ρ y)=algebraMap A C (φ y) :=
    IsLocalizedModule.map_apply (Submonoid.powers r.val) ρ a φ y
  let e := (OpenLineSectionBasis318.sections L.object
    (AffineLineModule318.basic A r.val) r.property.some).symm
  change ρ (φ s • x)=ρ (φ x • s)
  rw [map_smul, map_smul, ← algebraMap_smul C, ← algebraMap_smul C,
    ← hψ s, ← hψ x]
  exact in_frame e ψ (ρ s) (ρ x)
end OriginalAffineRankOneCommutation318
