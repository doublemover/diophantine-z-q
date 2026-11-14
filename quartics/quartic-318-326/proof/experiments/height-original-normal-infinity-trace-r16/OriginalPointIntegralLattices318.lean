module
public import OriginalIntrinsicPointModule318
public import OriginalIntrinsicFiberFrameTransport318
public section
noncomputable section
namespace OriginalPointIntegralLattices318
open NumberField AlgebraicGeometry ActualFinitePlaceIntegers318 OriginalAllPlaceProducedNorms318
open OriginalIntrinsicPointModule318
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ k : Fin 5,ContactRadical318.forms u v k≠0) (i j : Fin 4)
  (w : FinitePlace (K c u v))
local notation "E" => pointModule c (t u v)
local notation "R" => Integers w
local instance : Module R E := Module.compHom E (algebraMap R (K c u v))
local instance : IsScalarTower R (K c u v) E := IsScalarTower.of_compHom ..
local instance (k : Fin 4) : Module R
    (OriginalArithmeticTensorFiber318.fiber c (t u v) (hn c u v hf) k) :=
  Module.compHom _ (algebraMap R (K c u v))
local instance (k : Fin 4) : IsScalarTower R (K c u v)
    (OriginalArithmeticTensorFiber318.fiber c (t u v) (hn c u v hf) k) := IsScalarTower.of_compHom ..

/-- Actual embedded integral lattice in the SINGLE original whole-point
K-module. This is not a separate scalar line for each branch. -/
@[expose] def lattice : Submodule R E :=
  (OriginalIntrinsicFiniteLattices318.lattice c u v hf i w).comap
    ((toArithmeticFiber c (t u v) (hn c u v hf) i).restrictScalars R).toLinearMap

lemma toArithmeticFiber_transition (x : E) :
    OriginalIntrinsicFiberFrameTransport318.comparison c (t u v) (hn c u v hf) i j
      (toArithmeticFiber c (t u v) (hn c u v hf) i x)=
        toArithmeticFiber c (t u v) (hn c u v hf) j x := by
  apply (OriginalArithmeticTensorFiber318.frame c (t u v) (hn c u v hf) j).injective
  rw [OriginalIntrinsicFiberFrameTransport318.frame_comparison]
  change ContactBicanonicalPointHeight318.frameScalar c (t u v) (hn c u v hf) i j*
      (OriginalArithmeticTensorFiber318.frame c (t u v) (hn c u v hf) i
        ((OriginalArithmeticTensorFiber318.frame c (t u v) (hn c u v hf) i).symm
          (frame c (t u v) (hn c u v hf) i x)))=
    OriginalArithmeticTensorFiber318.frame c (t u v) (hn c u v hf) j
      ((OriginalArithmeticTensorFiber318.frame c (t u v) (hn c u v hf) j).symm
        (frame c (t u v) (hn c u v hf) j x))
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,frame_transition c (t u v) (hn c u v hf) i j x]

/-- Equality of actual submodules of ONE fixed geometric point fiber,
not only an isomorphism between separately named lattice modules. -/
theorem lattice_independent : lattice c u v hf j w=lattice c u v hf i w := by
  apply Submodule.ext
  intro x
  change toArithmeticFiber c (t u v) (hn c u v hf) j x∈
    OriginalIntrinsicFiniteLattices318.lattice c u v hf j w ↔ _
  rw [←toArithmeticFiber_transition c u v hf i j x]
  have h := congrArg (fun L => toArithmeticFiber c (t u v) (hn c u v hf) i x∈L)
    (OriginalIntrinsicFiberFrameTransport318.lattice_transport c i j u v hf w)
  exact Iff.of_eq h

@[expose] def latticeMap : lattice c u v hf i w →ₗ[R]
    OriginalIntrinsicFiniteLattices318.lattice c u v hf i w :=
  (((toArithmeticFiber c (t u v) (hn c u v hf) i).restrictScalars R).toLinearMap.comp
    (lattice c u v hf i w).subtype).codRestrict _ (fun x => x.property)
lemma latticeMap_bijective : Function.Bijective (latticeMap c u v hf i w) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact (toArithmeticFiber c (t u v) (hn c u v hf) i).injective (congrArg Subtype.val h)
  · intro y
    refine ⟨⟨(toArithmeticFiber c (t u v) (hn c u v hf) i).symm y.val,?_⟩,?_⟩
    · change toArithmeticFiber c (t u v) (hn c u v hf) i
        ((toArithmeticFiber c (t u v) (hn c u v hf) i).symm y.val)∈_
      simpa only [LinearEquiv.apply_symm_apply] using y.property
    · apply Subtype.ext
      exact (toArithmeticFiber c (t u v) (hn c u v hf) i).apply_symm_apply y.val

/-- Produced actual free rank-one valuation-ring lattice on the original
point line at every finite place, including all excluded primes. -/
@[expose] def basis : R ≃ₗ[R] lattice c u v hf i w :=
  (OriginalIntrinsicFiniteLattices318.basis c u v hf i w).trans
    (LinearEquiv.ofBijective (latticeMap c u v hf i w)
      (latticeMap_bijective c u v hf i w)).symm

theorem original_sections_mem (n : Fin 2) :
    globalElement c (t u v) (![ContactScaledBicanonicalPoint318.scaledQ0 c,
      ContactScaledBicanonicalPoint318.scaledQ1 c] n)∈lattice c u v hf i w := by
  change toArithmeticFiber c (t u v) (hn c u v hf) i _∈_
  rw [toArithmeticFiber_global]
  exact OriginalIntrinsicFiniteLattices318.original_global_sections_mem c u v hf i w n
end OriginalPointIntegralLattices318
