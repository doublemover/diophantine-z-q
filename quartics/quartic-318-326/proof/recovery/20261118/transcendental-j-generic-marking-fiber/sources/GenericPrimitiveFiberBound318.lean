module
public import TranscendentalJGenericFiber318
public import CanonicalGeometricMarkingEvaluation318
public section
noncomputable section
namespace GenericPrimitiveFiberBound318
open TranscendentalJGenericFiber318 OpenJComplexEvaluation318
open InvariantBaseChange318 OpenJAnalyticPoints318
variable (N:ℕ) [NeZero N]

def τ : UpperHalfPlane := (exists_period 0).choose
theorem h : Admissible τ := (exists_period 0).choose_spec.2.1
theorem ht : Transcendental ℤ (ActualQJ318.jInvariant τ) :=
  (exists_period 0).choose_spec.2.2

abbrev Mark := {P : (fiber N τ h).toAffine.Point // addOrderOf P=N}
local instance : Algebra (K N) ℂ := (embedding N τ h ht).toAlgebra

/-- Pointwise arithmetic moduli input uses the literal exact-order point,
not an injection over a polarized high-j region or an assumed function-field
degree. Agreement of the point assignment with scalar multiplication is
required for its actual action on coordinate functions. -/
theorem rank (H:Subgroup (ZMod N)ˣ) (B:Type*) [CommRing B] [Algebra (K N) B]
    [Module.Finite (K N) B] [Algebra.Etale (K N) B]
    (ρ:H→B≃ₐ[K N]B)
    (pt: Mark N → PrimeSpectrum (CanonicalGeometricMarkingEvaluation318.C (K N) ℂ B))
    (surj:Function.Surjective pt)
    (diamond : ∀ (u:H) (P Q : Mark N), P.val=(u.val:ZMod N).val • Q.val →
      pt P=(pt Q).comap (baseAction ℂ ρ u).toAlgHom) :
    (Module.finrank (K N) (invariants ρ):ℝ)≤(N:ℝ)*H.index*EulerIndex318.eulerProduct N := by
  let e := primitiveEquiv N τ h N
  let f := pt ∘ e
  have he : ∀ (u:H) x, f (u • x)=(f x).comap (baseAction ℂ ρ u).toAlgHom := by
    intro u x
    apply diamond
    change torsionMap N τ h N (PrimitiveDiamond318.scalar N u.val x.val) =
      _ • torsionMap N τ h N x.val
    rw [PrimitiveDiamond318.scalar_eq_nsmul, map_nsmul]
  have hr := CanonicalGeometricMarkingEvaluation318.rank H ℂ ρ f he
    (surj.comp e.surjective)
  exact (Nat.cast_le.mpr hr).trans (ActualGammaHIndexUpper318.gammaH_index N H)

end GenericPrimitiveFiberBound318
