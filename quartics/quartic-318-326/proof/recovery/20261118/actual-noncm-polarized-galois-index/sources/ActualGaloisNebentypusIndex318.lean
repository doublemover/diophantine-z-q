module
public import PolarizedRepeatedConstituent318
public import ModularIndex318
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public section
noncomputable section
namespace ActualGaloisNebentypusIndex318
open Matrix PolarizedRepeatedConstituent318
abbrev Ω := AlgebraicClosure ℚ
abbrev G := Ω ≃ₐ[ℚ] Ω

/-- The finite quotient is the actual action on Nth roots of unity in a
cyclotomic subfield of the fixed algebraic closure. -/
def cycloMod (N : ℕ) [NeZero N] (T : IntermediateField ℚ Ω)
    [IsCyclotomicExtension {N} ℚ T] : G →* (ZMod N)ˣ := by
  letI := IsCyclotomicExtension.isGalois ({N}:Set ℕ) ℚ T
  exact (IsCyclotomicExtension.autEquivPow T
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))).toMonoidHom.comp
      (AlgEquiv.restrictNormalHom T)

theorem cycloMod_surjective (N : ℕ) [NeZero N] (T : IntermediateField ℚ Ω)
    [IsCyclotomicExtension {N} ℚ T] : Function.Surjective (cycloMod N T) := by
  letI := IsCyclotomicExtension.isGalois ({N}:Set ℕ) ℚ T
  exact (IsCyclotomicExtension.autEquivPow T
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))).surjective.comp
      (AlgEquiv.restrictNormalHom_surjective (F:=ℚ) (K₁:=T) (E:=Ω))

abbrev doubled {k : Type*} [Field k] (R : M₂ k) := Matrix.fromBlocks R 0 0 R
abbrev gram {k : Type*} [Field k] (a b : k) (X Y : M₂ k) :=
  Matrix.fromBlocks (alt a) X Y (alt b)

/-- The original character-kernel index appearing in the `Γ_H` cover, now
using the absolute Galois action on genuine fields and the alternating
polarization on the two equal constituents over F. Not a construction of
the modular form, its Galois representation or the polarization itself. -/
theorem index (N : ℕ) [NeZero N] (T F : IntermediateField ℚ Ω)
    [IsCyclotomicExtension {N} ℚ T] [IsGalois ℚ F] [FiniteDimensional ℚ F]
    {k : Type*} [Field k] (ε : (ZMod N)ˣ →* kˣ)
    (χ : G →* kˣ) (r : G →* Matrix.GeneralLinearGroup (Fin 2) k)
    (hdet : ∀σ, Matrix.GeneralLinearGroup.det (r σ)=ε (cycloMod N T σ)*χ σ)
    (X Y : M₂ k) (a b : k) (hn : (gram a b X Y).det≠0)
    (hpolar : ∀σ : G, AlgEquiv.restrictNormalHom F σ=1 →
      (doubled (r σ).val).transpose * gram a b X Y * doubled (r σ).val =
        (χ σ : k) • gram a b X Y)
    (S : ℕ) (hfield : Module.finrank ℚ F≤2304*S) : ε.ker.index≤4608*S := by
  classical
  letI : Fintype (F ≃ₐ[ℚ] F) := Fintype.ofFinite _
  apply NebentypusOrder318.determinant_finite_index_bound (AlgEquiv.restrictNormalHom F)
    (cycloMod N T) (cycloMod_surjective N T) ε χ (Matrix.GeneralLinearGroup.det.comp r) hdet
  · intro σ hσ
    apply Units.ext
    exact square (r σ).val X Y a b (χ σ:k) hn (hpolar σ hσ)
  · simpa [←Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank] using hfield

/-- Direct interface to the actual modular j-cover degree consumer. The
conductor/support inputs and j-cover index identity remain explicit; no
independent kernel index, Galois-group cardinality, cyclotomic surjectivity,
or square-determinant inequality is assumed. -/
theorem cover_degree (N : ℕ) [NeZero N] (T F : IntermediateField ℚ Ω)
    [IsCyclotomicExtension {N} ℚ T] [IsGalois ℚ F] [FiniteDimensional ℚ F]
    {k : Type*} [Field k] (ε : (ZMod N)ˣ →* kˣ)
    (χ : G →* kˣ) (r : G →* Matrix.GeneralLinearGroup (Fin 2) k)
    (hdet : ∀σ, Matrix.GeneralLinearGroup.det (r σ)=ε (cycloMod N T σ)*χ σ)
    (X Y : M₂ k) (a b : k) (hn : (gram a b X Y).det≠0)
    (hpolar : ∀σ : G, AlgEquiv.restrictNormalHom F σ=1 →
      (doubled (r σ).val).transpose * gram a b X Y * doubled (r σ).val =
        (χ σ : k) • gram a b X Y)
    (S : ℕ) (hfield : Module.finrank ℚ F≤2304*S) (C d : ℝ) (hS : 0<S) (hC : 0<C)
    (hs : ∀p∈N.primeFactors,p∣S) (hN : (N:ℝ)≤C*(S:ℝ)^2)
    (hd : d≤(N:ℝ)*ε.ker.index*EulerIndex318.eulerProduct N) :
    d<2^14*C*(S:ℝ)^((97:ℝ)/32) :=
  EulerIndex318.index_bound_of_le N S ε.ker.index C d hS hC hs hN
    (index N T F ε χ r hdet X Y a b hn hpolar S hfield) hd
end ActualGaloisNebentypusIndex318
