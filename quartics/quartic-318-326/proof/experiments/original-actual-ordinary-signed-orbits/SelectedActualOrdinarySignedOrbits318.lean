module
public import SelectedMarkedPeriodCoordinate318
public import ActualJOrbitClassification318
public section
noncomputable section

open scoped MatrixGroups
open OpenJComplexEvaluation318 MarkedPeriod318 EllipticTorsion318
open ModularTorusTransport318 ModularTorsionTransport318

namespace SelectedActualOrdinarySignedOrbits318

/-- The simultaneously signed mark is the only loss from x, excluding
the unrelated infinity value x=0 by genuine nonzero point hypotheses. -/
theorem same_x_sign (τ : UpperHalfPlane)
    (P Q : (ModularWeierstrass318.curve τ).toAffine.Point)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : CanonicalXModularity318.pointX P = CanonicalXModularity318.pointX Q) :
    P = Q ∨ P = -Q := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some x y h =>
    cases Q with
    | zero => exact False.elim (hQ rfl)
    | some x' y' h' => exact WeierstrassCurve.Affine.Point.X_eq_iff.mp hx

theorem std_nonzero (N : ℕ) [NeZero N] (hN : 1 < N) (τ : UpperHalfPlane) :
    standardPoint N τ ≠ 0 := by
  intro h
  have ho := standardPoint_order N τ
  rw [h,addOrderOf_zero] at ho
  omega

/-- An arbitrary composite-level integral matrix preserving the
mark up to sign lies in Gamma1 up to the central sign, not Gamma0
in general. The inverse transpose convention is the actual one. -/
theorem matrix_signed (N : ℕ) (g : SL(2,ℤ))
    (h : residueMap g N (standardLabel N) = standardLabel N ∨
      residueMap g N (standardLabel N) = -(standardLabel N)) :
    g ∈ CongruenceSubgroup.Gamma1 N ∨ -g ∈ CongruenceSubgroup.Gamma1 N := by
  rcases h with hp | hn
  · exact Or.inl ((label_stabilizer N g).mp hp)
  · right
    apply (label_stabilizer N (-g)).mp
    have hflip : residueMap (-g) N (standardLabel N) = -(residueMap g N (standardLabel N)) := by
      ext <;> simp [residueMap,standardLabel,Matrix.SpecialLinearGroup.coe_neg,Matrix.neg_apply]
    rw [hflip,hn,neg_neg]

/-- Equality of the same branch-free x over the same actual modular j
separates the complete original Gamma1(N) orbits. -/
theorem coordinates_eq_iff_orbit (N : ℕ) [NeZero N] (hN : 1 < N)
    (τ ν : UpperHalfPlane) (hτ : Admissible τ) (hν : Admissible ν) :
    (ActualQJ318.jInvariant τ = ActualQJ318.jInvariant ν ∧
      SelectedMarkedPeriodCoordinate318.arithmeticX N τ =
        SelectedMarkedPeriodCoordinate318.arithmeticX N ν) ↔
    ∃ g : SL(2,ℤ), g ∈ CongruenceSubgroup.Gamma1 N ∧ g • τ = ν := by
  constructor
  · rintro ⟨hj,hx⟩
    obtain ⟨g,rfl⟩ := ActualJOrbitClassification318.exists_modular_of_j_eq τ ν hj
    let e := pointAddEquiv g τ
    let P := e (standardPoint N τ)
    let Q := standardPoint N (g • τ)
    have hQ : Q ≠ 0 := std_nonzero N hN _
    have hP : P ≠ 0 := by
      intro h
      exact std_nonzero N hN τ (e.injective (h.trans (map_zero e).symm))
    have hs := CanonicalXModularity318.scale_transform
      ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) g) ⟨g,rfl⟩ τ
    change CanonicalXScale318.scale (g • τ : UpperHalfPlane) = _ at hs
    have hnτ := CanonicalXScale318.scale_ne_zero N τ hτ
    have hnν := CanonicalXScale318.scale_ne_zero N (g • τ) hν
    have hx' : CanonicalXModularity318.pointX P = CanonicalXModularity318.pointX Q := by
      change CanonicalXModularity318.pointX (pointAddEquiv g τ (standardPoint N τ)) = _
      rw [CanonicalXModularity318.pointX_transport]
      symm
      calc
        CanonicalXModularity318.pointX Q =
            SelectedMarkedPeriodCoordinate318.arithmeticX N (g • τ) *
              CanonicalXScale318.scale (g • τ : UpperHalfPlane) := by
          unfold SelectedMarkedPeriodCoordinate318.arithmeticX
          rw [div_mul_cancel₀ _ hnν] <;> rfl
        _ = _ := by
          rw [← hx,hs]
          unfold SelectedMarkedPeriodCoordinate318.arithmeticX
          field_simp [hnτ] <;> ring
    have hsign : residueMap g N (standardLabel N) = standardLabel N ∨
        residueMap g N (standardLabel N) = -(standardLabel N) := by
      rcases same_x_sign (g • τ) P Q hP hQ hx' with hp | hm
      · left
        apply torsionMap_injective (g • τ) N
        rw [← torsion_transport]
        exact hp
      · right
        apply torsionMap_injective (g • τ) N
        rw [map_neg,← torsion_transport]
        exact hm
    rcases matrix_signed N g hsign with hg | hg
    · exact ⟨g,hg,rfl⟩
    · exact ⟨-g,hg,ModularGroup.SL_neg_smul g τ⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨(ActualJInvariant318.modular_invariant
      ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) g) ⟨g,rfl⟩ τ).symm,
      (SelectedMarkedPeriodCoordinate318.arithmeticX_invariant N g hg τ).symm⟩

end SelectedActualOrdinarySignedOrbits318

#print axioms SelectedActualOrdinarySignedOrbits318.matrix_signed
#print axioms SelectedActualOrdinarySignedOrbits318.coordinates_eq_iff_orbit
