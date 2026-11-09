module
public import IntegralBranchCoordinates318
public import BicanonicalCoefficientIdentity318
public section
noncomputable section
namespace IntegralBranchBicanonical318
open Polynomial IntegralSourceBranches318 IntegralBranchDenominatorCover318
open IntegralBranchCoordinates318 IntegralBranchLocalization318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ) (i : Fin 4)
@[expose] def quartic : R[X] := ∏ j : Fin 4, (X - C (contacts R j))
@[expose] def sourceP : B R c i :=
  algebraMap R[X] (B R c i) (quartic R)
@[expose] def coefficient0 : B R c i :=
  (4 * algebraMap R (B R c i) (twistUnit R c i : R) *
    algebraMap R (B R c i) (↑(c i)⁻¹ : R)) *
      IsLocalization.Away.invSelf (denominator R c i)
@[expose] def coefficient1 : B R c i := sourceT R c i * coefficient0 R c i

/-- A literal polynomial factorization at every original contact, with all twists retained. -/
theorem factor_product_polynomial :
    (X - C (contacts R i)) * twisted R c i =
      C (twistUnit R c i : R) * quartic R := by
  rw [twisted_factor]
  have h : (X - C (contacts R i)) * untwisted R i = quartic R := by
    fin_cases i <;>
      simp [untwisted,quartic,indices,contacts,Fin.prod_univ_succ] <;> ring
  calc
    (X - C (contacts R i)) * (C (twistUnit R c i : R) * untwisted R i) =
        C (twistUnit R c i : R) * ((X - C (contacts R i)) * untwisted R i) := by ring
    _ = _ := by rw [h]

theorem factor_product :
    (sourceT R c i - algebraMap R (B R c i) (contacts R i)) *
      algebraMap (SourceOrder R c) (B R c i) (denominator R c i) =
        algebraMap R (B R c i) (twistUnit R c i : R) * sourceP R c i := by
  have h := congrArg (algebraMap R[X] (B R c i)) (factor_product_polynomial R c i)
  have hC (a : R) : algebraMap R[X] (B R c i) (C a) = algebraMap R (B R c i) a :=
    (IsScalarTower.algebraMap_apply R R[X] (B R c i) a).symm
  simpa only [map_mul,map_sub,hC,sourceT,denominator,sourceP,
    ←IsScalarTower.algebraMap_apply] using h

/-- The original quartic times the regular branch coefficient is exactly
the square of the real ramified-coordinate differential coefficient. -/
theorem cleared :
    sourceP R c i * coefficient0 R c i =
      (2 * algebraMap R (B R c i) (↑(c i)⁻¹ : R) * sourceCoordinate R c i)^2 := by
  exact BicanonicalCoefficientIdentity318.finite_cleared _ _ _ _ _ _ _ _
    (factor_product R c i)
    (IsLocalization.Away.mul_invSelf (denominator R c i))
    (coordinate_square R c i)

theorem cleared_frame (h2 : IsUnit (2 : R)) :
    sourceP R c i * coefficient0 R c i =
      (sourceFrame R c i h2 (KaehlerDifferential.D R (B R c i) (sourceT R c i)))^2 := by
  rw [frame_D_sourceT]
  exact cleared R c i

/-- The first coefficient is a unit on the entire integral contact chart. -/
theorem coefficient0_unit (h2 : IsUnit (2 : R)) : IsUnit (coefficient0 R c i) := by
  have h4 : IsUnit (4 : B R c i) := by
    have h4R : IsUnit (4 : R) := by
      simpa only [show (2 : R)^2 = (4 : R) by ring] using h2.pow 2
    simpa only [map_ofNat] using h4R.map (algebraMap R (B R c i))
  have hinv : IsUnit (IsLocalization.Away.invSelf (S := B R c i) (denominator R c i)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨algebraMap (SourceOrder R c) (B R c i) (denominator R c i),?_⟩
    rw [mul_comm,IsLocalization.Away.mul_invSelf]
  exact ((h4.mul ((twistUnit R c i).isUnit.map (algebraMap R (B R c i)))).mul
    (((c i)⁻¹).isUnit.map (algebraMap R (B R c i)))).mul hinv

end IntegralBranchBicanonical318
