module
public import EtaleHighFiberDegree318
public import ActualLargeJMarkedFiber318
public import ActualGaloisNebentypusIndex318
public import Mathlib.LinearAlgebra.Dimension.Localization
public section
noncomputable section
namespace ActualEtaleMarkedDegree318
open scoped Polynomial
open EtaleHighFiberDegree318 ActualLargeJMarkedFiber318

/-- Replace an assumed covering-degree inequality by a scheme-theoretic
finite free étale chart of the genuine curve on a nonempty j-open and a
point-level comparison. Only injection on its geometric points into the
specified *actual* marked analytic j-fibre is used. No surjectivity,
number-of-sheets or identification of either rank with a numeral is given.
The two fields are the compatible fraction fields of the affine charts. -/
theorem degree (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (f : ℂ[X]) (hf : f≠0)
    (A K L : Type*) [CommRing A] [Field K] [Field L] [Algebra (Base f) A]
    [Module.Free (Base f) A] [Module.Finite (Base f) A] [Algebra.Etale (Base f) A]
    [Algebra (Base f) K] [Algebra A L] [Algebra K L] [Algebra (Base f) L]
    [IsScalarTower (Base f) K L] [IsScalarTower (Base f) A L]
    [IsFractionRing (Base f) K] [IsFractionRing A L]
    (compare : ∀(c:ℂ) (hc:f.eval c≠0),
      Nonempty (PrimeSpectrum (FiberAlgebra f A c hc) ↪ Fiber N H c)) :
    (Module.finrank K L:ℝ)≤(N:ℝ)*H.index*EulerIndex318.eulerProduct N := by
  obtain ⟨B,hB⟩ := finite_fiber
  obtain ⟨c,hc,hn⟩ := arbitrarily_high f hf B
  obtain ⟨hfin,hcard⟩ := hB N H c hc
  letI : Finite (Fiber N H c) := hfin
  obtain ⟨i⟩ := compare c hn
  have hh := (Nat.card_le_card_of_injective i i.injective).trans hcard
  rw [card_actual,←IsFractionRing.finrank_eq (Base f) K A L] at hh
  exact (Nat.cast_le.mpr hh).trans (ActualGammaHIndexUpper318.gammaH_index N H)

/-- Sharp degree exponent for a modular-cover chart on the literal
character kernel, using the already proved three independent pieces:
polarization and Galois action, congruence index, and high finite étale
fibre comparison. No hypothesis regarding the given cover degree bound or
finite Dirichlet-character kernel index occurs. -/
theorem sharp {N:ℕ} [NeZero N] {k:Type*} [Field k] (ε:(ZMod N)ˣ→*kˣ)
    (f : ℂ[X]) (hf:f≠0)
    (A K L : Type*) [CommRing A] [Field K] [Field L] [Algebra (Base f) A]
    [Module.Free (Base f) A] [Module.Finite (Base f) A] [Algebra.Etale (Base f) A]
    [Algebra (Base f) K] [Algebra A L] [Algebra K L] [Algebra (Base f) L]
    [IsScalarTower (Base f) K L] [IsScalarTower (Base f) A L]
    [IsFractionRing (Base f) K] [IsFractionRing A L]
    (compare : ∀(c:ℂ) (hc:f.eval c≠0),
      Nonempty (PrimeSpectrum (FiberAlgebra f A c hc) ↪ Fiber N ε.ker c))
    (T F : IntermediateField ℚ ActualGaloisNebentypusIndex318.Ω)
    [IsCyclotomicExtension {N} ℚ T] [IsGalois ℚ F] [FiniteDimensional ℚ F]
    (χ : ActualGaloisNebentypusIndex318.G →* kˣ)
    (r : ActualGaloisNebentypusIndex318.G →* Matrix.GeneralLinearGroup (Fin 2) k)
    (hdet : ∀σ, Matrix.GeneralLinearGroup.det (r σ)=ε (ActualGaloisNebentypusIndex318.cycloMod N T σ)*χ σ)
    (X Y : PolarizedRepeatedConstituent318.M₂ k) (a b:k)
    (hn : (ActualGaloisNebentypusIndex318.gram a b X Y).det≠0)
    (hpolar : ∀σ:ActualGaloisNebentypusIndex318.G, AlgEquiv.restrictNormalHom F σ=1 →
      (ActualGaloisNebentypusIndex318.doubled (r σ).val).transpose *
        ActualGaloisNebentypusIndex318.gram a b X Y *
        ActualGaloisNebentypusIndex318.doubled (r σ).val =
        (χ σ:k) • ActualGaloisNebentypusIndex318.gram a b X Y)
    (S:ℕ) (hfield:Module.finrank ℚ F≤2304*S) (C:ℝ) (hS:0<S) (hC:0<C)
    (hs:∀p∈N.primeFactors,p∣S) (hN:(N:ℝ)≤C*(S:ℝ)^2) :
    (Module.finrank K L:ℝ)<2^14*C*(S:ℝ)^((97:ℝ)/32) :=
  ActualGaloisNebentypusIndex318.cover_degree N T F ε χ r hdet X Y a b hn hpolar S hfield
    C (Module.finrank K L) hS hC hs hN (degree N ε.ker f hf A K L compare)
end ActualEtaleMarkedDegree318
