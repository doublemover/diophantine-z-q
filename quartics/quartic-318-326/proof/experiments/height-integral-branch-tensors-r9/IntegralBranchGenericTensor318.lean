module
public import IntegralBranchBicanonical318
public import VerticalCotangentSections318
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace IntegralBranchGenericTensor318
open Polynomial IntegralSourceBranches318 IntegralBranchCoordinates318 IntegralBranchBicanonical318
open IntegralBranchLocalization318 IntegralCotangentTensor318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ) (i : Fin 4) (h2 : IsUnit (2 : R))

/-- Whole-chart integral tensors, with the original J-squared scaling. -/
@[expose] def tensor0 : KaehlerDifferential R (B R c i) ⊗[B R c i] KaehlerDifferential R (B R c i) :=
  (squareFrame (sourceFrame R c i h2)).symm
    ((VerticalSection318.J : B R c i)^2 * coefficient0 R c i)
@[expose] def tensor1 : KaehlerDifferential R (B R c i) ⊗[B R c i] KaehlerDifferential R (B R c i) :=
  (squareFrame (sourceFrame R c i h2)).symm
    ((VerticalSection318.J : B R c i)^2 * coefficient1 R c i)

variable [IsDomain R] [IsDomain (B R c i)]
  (K : Type*) [Field K] [Algebra (B R c i) K] [Algebra R K]
  [IsScalarTower R (B R c i) K] [IsFractionRing (B R c i) K]

/-- Nonvanishing of the real quartic follows from the actual flat source
and its monic polynomial, not a supplied generic nonvanishing assumption. -/
theorem sourceP_ne_zero : sourceP R c i ≠ 0 := by
  letI : Module.Free R[X] (SourceOrder R c) := (FourRootOrder318.finite_free _).2
  letI : Module.Flat R[X] (B R c i) := Module.Flat.trans R[X] (SourceOrder R c) (B R c i)
  letI : Module.IsTorsionFree R[X] (B R c i) := Module.Flat.isTorsionFree
  have hm : (quartic R).Monic := Polynomial.monic_prod_of_monic _ _
    (fun j _ => Polynomial.monic_X_sub_C _)
  simpa only [sourceP,map_zero] using
    (FaithfulSMul.algebraMap_injective R[X] (B R c i)).ne hm.ne_zero

theorem mapped_quartic :
    algebraMap (B R c i) K (sourceP R c i) =
      VerticalSection318.denominator (algebraMap (B R c i) K (sourceT R c i)) := by
  have hC (a : R) : algebraMap R[X] (B R c i) (C a) = algebraMap R (B R c i) a :=
    (IsScalarTower.algebraMap_apply R R[X] (B R c i) a).symm
  have hX : algebraMap R[X] (B R c i) X = sourceT R c i :=
    IsScalarTower.algebraMap_apply R[X] (SourceOrder R c) (B R c i) X
  simp only [sourceP,quartic,map_prod,map_sub,hC,hX]
  simp only [VerticalSection318.denominator,contacts,VerticalSection318.contacts,
    Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,map_zero,map_ofNat,map_neg,Int.cast_zero,Int.cast_ofNat,Int.cast_neg]
  ring

theorem coefficient0_image :
    algebraMap (B R c i) K ((VerticalSection318.J : B R c i)^2 * coefficient0 R c i) =
      VerticalSection318.section0 (FractionSourceSections318.derived (sourceFrame R c i h2))
        (algebraMap (B R c i) K (sourceT R c i)) := by
  have hc := congrArg (algebraMap (B R c i) K) (cleared_frame R c i h2)
  rw [map_mul,map_pow] at hc
  have hp : algebraMap (B R c i) K (sourceP R c i) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B R c i) K).ne (sourceP_ne_zero R c i)
  have hd := FractionSourceSections318.derived_integral (K := K)
    (sourceFrame R c i h2) (sourceT R c i)
  change FractionSourceSections318.derived (sourceFrame R c i h2)
    (algebraMap (B R c i) K (sourceT R c i)) =
      algebraMap (B R c i) K
        (sourceFrame R c i h2 (KaehlerDifferential.D R (B R c i) (sourceT R c i))) at hd
  rw [VerticalSection318.section0,hd,←mapped_quartic R c i K]
  apply (eq_div_iff hp).mpr
  rw [map_mul,map_pow,map_intCast]
  calc
    (VerticalSection318.J : K)^2 * algebraMap (B R c i) K (coefficient0 R c i) *
        algebraMap (B R c i) K (sourceP R c i) =
      (VerticalSection318.J : K)^2 *
        (algebraMap (B R c i) K (sourceP R c i) *
          algebraMap (B R c i) K (coefficient0 R c i)) := by ring
    _ = _ := by rw [hc]

theorem coefficient1_image :
    algebraMap (B R c i) K ((VerticalSection318.J : B R c i)^2 * coefficient1 R c i) =
      VerticalSection318.section1 (FractionSourceSections318.derived (sourceFrame R c i h2))
        (algebraMap (B R c i) K (sourceT R c i)) := by
  rw [VerticalSection318.section1,←coefficient0_image R c i h2 K]
  simp only [coefficient1,map_mul,map_pow,map_intCast]
  ring

/-- Exact generic images of the two actual whole-branch integral tensors.
The generic field is the fraction field of this same source chart. -/
theorem tensor_images :
    IntegralCotangentTensor318.map (sourceFrame R c i h2) (tensor0 R c i h2) =
      VerticalCotangentSections318.q0 (R := R)
        (algebraMap (B R c i) K (sourceT R c i)) ∧
    IntegralCotangentTensor318.map (sourceFrame R c i h2) (tensor1 R c i h2) =
      VerticalCotangentSections318.q1 (R := R)
        (algebraMap (B R c i) K (sourceT R c i)) := by
  constructor
  · apply (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) (sourceFrame R c i h2))).injective
    rw [frame_map,tensor0,LinearEquiv.apply_symm_apply,VerticalCotangentSections318.q0_coefficient]
    exact coefficient0_image R c i h2 K
  · apply (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) (sourceFrame R c i h2))).injective
    rw [frame_map,tensor1,LinearEquiv.apply_symm_apply,VerticalCotangentSections318.q1_coefficient]
    exact coefficient1_image R c i h2 K

end IntegralBranchGenericTensor318
