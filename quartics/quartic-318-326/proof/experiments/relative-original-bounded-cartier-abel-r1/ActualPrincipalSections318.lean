module
public import PrincipalCocycleSplit318
public import Mathlib.AlgebraicGeometry.AffineScheme

public section
noncomputable section
namespace ActualPrincipalSections318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PrincipalFractionClearing318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : CommRingCat.{0}} [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

abbrev Sections (f : R) := (Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))

omit [IsDomain R] in
theorem sections_eq_original (f : R) : Sections f = Γ(Spec R, PrimeSpectrum.basicOpen f) := rfl

/-- The original structure-sheaf basic-open section embedded in the actual fraction field. -/
@[expose] def embed (f : R) (hf : f ≠ 0) : Sections f →ₐ[R] K :=
  Localization.mapToFractionRing K (Submonoid.powers f) (Sections f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

theorem embed_injective (f : R) (hf : f ≠ 0) : Function.Injective (embed (K:=K) f hf) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  constructor
  · intro h
    exact congrArg (algebraMap R K)
      (IsLocalization.injective (Sections f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf) h)
  · intro h
    exact congrArg (algebraMap R (Sections f)) ((IsFractionRing.injective R K) h)

theorem range_embed (f : R) (hf : f ≠ 0) : (embed (K:=K) f hf).range = away f hf := by
  ext x
  exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField K
    (Submonoid.powers f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf) (Sections f) x)

@[expose] def restrict {f g : R} (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    Sections f →+* Sections g := ((Spec.structureSheaf R).obj.map (homOfLE h).op).hom

/-- Every original restriction agrees with the same rational function in the fraction field. -/
theorem embed_restrict {f g : R} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (s : Sections f) :
    embed g hg (restrict h s) = embed (K:=K) f hf s := by
  have he : (embed (K:=K) g hg).toRingHom.comp (restrict h) = (embed f hf).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    change embed g hg (algebraMap R (Sections g) r) = embed f hf (algebraMap R (Sections f) r)
    simp only [AlgHom.commutes]
  exact RingHom.congr_fun he s

/-- Every regular fraction used by the algebraic contraction is an original basic-open section. -/
theorem exists_section (f : R) (hf : f ≠ 0) (x : K) (hx : x ∈ away f hf) :
    ∃ s : Sections f, embed f hf s = x := by
  rw [← range_embed f hf] at hx
  exact hx

end ActualPrincipalSections318
