module
public import OriginalAllPlaceRootBounds318
public import DVRRootParityComparison318
public section
noncomputable section
namespace OriginalReciprocalParity318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open ActualFinitePlaceIntegers318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : Data c t w)

/-- At a nonintegral original coordinate, all four normalized twist
parities agree. The reciprocal factor is common, and each1-a_i/t is a
UNIT in the actual valuation ring, including at collision/dyadic primes. -/
theorem parity_eq (ht : ¬w (t : K c t)≤1) (i j : Fin 4) : D.exponent i=D.exponent j := by
  obtain ⟨T,z,ht0,hT,hz,hrel,hr⟩ := OriginalAllPlaceRootBounds318.reciprocal_coordinates c t w D ht
  have hT0 : T≠0 := by
    intro h
    rw [h,map_zero] at hT
    exact inv_ne_zero ht0 hT.symm
  have hTn : ¬IsUnit T := by
    rintro ⟨U,hU⟩
    have hb := integer_bound w (↑U⁻¹ : V c t w)
    rw [map_units_inv,hU,hT,inv_inv] at hb
    exact ht hb
  have hunit (k : Fin 4) : IsUnit
      (1-IntegralSourceBranches318.contacts (V c t w) k*T) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      (fun h => hTn (isUnit_of_mul_isUnit_right h))
  let U : Fin 4 → (V c t w)ˣ := fun k => D.unit k*(hunit k).unit
  have hsquare (k : Fin 4) : (algebraMap (V c t w) (K c t) (z k))^2 =
      algebraMap (V c t w) (K c t) ((U k : V c t w)*D.pi^(D.exponent k : ℕ)*T) := by
    rw [←map_pow,hrel k]
    apply congrArg (algebraMap (V c t w) (K c t))
    simp only [Data.coefficients,U,Units.val_mul,(hunit k).unit_spec]
    ring
  exact DVRRootParityComparison318.parity_eq (V c t w) (K c t) D.pi D.irreducible
    (U i) (U j) T hT0 (D.exponent i) (D.exponent j)
    (algebraMap (V c t w) (K c t) (z i)) (algebraMap (V c t w) (K c t) (z j))
    (hsquare i) (hsquare j)

/-- The all-even/all-odd case split is internally proved for the SAME
original point, rather than requested as an arithmetic-model hypothesis. -/
theorem even_or_odd (ht : ¬w (t : K c t)≤1) :
    (∀ i,D.exponent i=0) ∨ (∀ i,D.exponent i=1) := by
  rcases (show ∀ e : Fin 2,e=0 ∨ e=1 from by decide) (D.exponent 0) with h|h
  · exact Or.inl (fun i => (parity_eq c t w D ht i 0).trans h)
  · exact Or.inr (fun i => (parity_eq c t w D ht i 0).trans h)
end OriginalReciprocalParity318
