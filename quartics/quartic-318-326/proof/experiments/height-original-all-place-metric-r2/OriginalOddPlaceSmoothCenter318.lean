module
public import OriginalAllPlaceRootBounds318
public import OddTwistDilatationCenter318
public section
noncomputable section
namespace OriginalOddPlaceSmoothCenter318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open FourRootPivot318 OddTwistDilatationEtale318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : Data c t w) (i : Fin 4)
abbrev a : V c t w := IntegralSourceBranches318.contacts (V c t w) i
abbrev otherUnit (j : Fin 3) : (V c t w)ˣ := D.unit (indices i j.succ)
abbrev otherContact (j : Fin 3) : V c t w :=
  IntegralSourceBranches318.contacts (V c t w) (indices i j.succ)
abbrev LocalChart := Chart (V c t w) D.pi (D.unit i) (a c t w i)
  (fun j => (otherUnit c t w D i j : V c t w)) (otherContact c t w i)

/-- The other normalized exponents are PRODUCED, not assumed: two odd
ones would force the uniformizer to divide their unit contact difference. -/
theorem other_exponents_zero (ht : w (t : K c t) ≤ 1)
    (hi : D.exponent i=1)
    (hsep : ∀ j : Fin 3,IsUnit (a c t w i-otherContact c t w i j)) :
    ∀ j : Fin 3,D.exponent (indices i j.succ)=0 := by
  obtain ⟨T,r,hT,hr,hrel⟩ := OriginalAllPlaceRootBounds318.finite_coordinates c t w D ht
  have hdi : D.pi ∣ T-a c t w i :=
    OddTwistDilatationCoordinates318.contact_difference_dvd D.pi D.irreducible
      (D.unit i) (a c t w i) T (r i) (by simpa [Data.coefficients,hi,a] using hrel i)
  intro j
  rcases (show ∀ e : Fin 2,e=0 ∨ e=1 from by decide) (D.exponent (indices i j.succ)) with hj|hj
  · exact hj
  · have hdj : D.pi ∣ T-otherContact c t w i j :=
      OddTwistDilatationCoordinates318.contact_difference_dvd D.pi D.irreducible
        (D.unit (indices i j.succ)) (otherContact c t w i j) T (r (indices i j.succ))
        (by simpa [Data.coefficients,hj,otherContact] using hrel (indices i j.succ))
    have hd : D.pi ∣ a c t w i-otherContact c t w i j := by
      convert dvd_sub hdj hdi using 1 <;> ring
    exact False.elim (D.irreducible.not_isUnit (isUnit_of_dvd_unit hd (hsep j)))

/-- At an original point with one odd normalized twist and three even
ones, an odd separated place has a PRODUCED smooth local model and
valuation-ring point. All four ORIGINAL signed root values are recovered
in their fixed original indices. No original twist needs valuation zero. -/
theorem exists_smooth_center
    (ht : w (t : K c t) ≤ 1)
    (hi : D.exponent i = 1)
    (h2 : IsUnit (2 : V c t w))
    (hsep : ∀ j : Fin 3,IsUnit (a c t w i-otherContact c t w i j)) :
    ∃ (z : V c t w) (f : LocalChart c t w D i →+* V c t w),
      Algebra.Smooth (V c t w) (LocalChart c t w D i) ∧
      (∀ k : V c t w,f (algebraMap (V c t w) (LocalChart c t w D i) k)=k) ∧
      algebraMap (V c t w) (K c t)
        (f (contactValue (V c t w) D.pi (D.unit i) (a c t w i)
          (fun j => (otherUnit c t w D i j : V c t w)) (otherContact c t w i)))=(t : K c t) ∧
      algebraMap (V c t w) (K c t) (D.pi*z)=D.normalizedRoots i ∧
      ∀ j : Fin 3,algebraMap (V c t w) (K c t)
        (f (ThreeRootCoordinates318.generator _ j))=D.normalizedRoots (indices i j.succ) := by
  have he := other_exponents_zero c t w D i ht hi hsep
  obtain ⟨T,r,hT,hr,hrel⟩ := OriginalAllPlaceRootBounds318.finite_coordinates c t w D ht
  have hy : (r i)^2 = (D.unit i : V c t w)*D.pi*(T-a c t w i) := by
    simpa [Data.coefficients,hi,a] using hrel i
  have hother (j : Fin 3) : (r (indices i j.succ))^2=
      (otherUnit c t w D i j : V c t w)*(T-otherContact c t w i j) := by
    simpa [Data.coefficients,he j,otherUnit,otherContact] using hrel (indices i j.succ)
  obtain ⟨z,hroots,hunits,hz,hsmooth,hzvalue,htvalue,hotherValue⟩ :=
    OddTwistDilatationCenter318.exists_smooth_center (V c t w) D.pi D.irreducible
      (D.unit i) (a c t w i) (otherUnit c t w D i) (otherContact c t w i)
      hsep T (r i) (fun j => r (indices i j.succ)) hy hother h2
  let f := (point (V c t w) D.pi (D.unit i) (a c t w i)
    (fun j => (otherUnit c t w D i j : V c t w)) (otherContact c t w i)
    z (fun j => r (indices i j.succ)) hroots hunits)
  refine ⟨z,f,hsmooth,?_,?_,?_,?_⟩
  · exact point_scalar (V c t w) D.pi (D.unit i) (a c t w i)
      (fun j => (otherUnit c t w D i j : V c t w)) (otherContact c t w i)
      z (fun j => r (indices i j.succ)) hroots hunits
  · change algebraMap (V c t w) (K c t) (_ _)=_
    rw [htvalue,hT]
  · rw [←hz,hr i]
  · intro j
    change algebraMap (V c t w) (K c t) (_ _)=_
    rw [hotherValue j,hr]
end OriginalOddPlaceSmoothCenter318
