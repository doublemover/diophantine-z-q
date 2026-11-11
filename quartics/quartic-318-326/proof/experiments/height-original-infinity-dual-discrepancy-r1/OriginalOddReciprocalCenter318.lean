module
public import OriginalReciprocalParity318
public import OddInfinitySmoothChart318
public section
noncomputable section
namespace OriginalOddReciprocalCenter318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open ActualFinitePlaceIntegers318 Polynomial
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
abbrev coefficients := OddInfinitySmoothChart318.coefficient (V c t w) D.pi D.unit
  (IntegralSourceBranches318.contacts (V c t w))
abbrev Ring := ThreePolynomialEtaleChart318.Chart (V c t w) (coefficients c t w D)

structure Center where
  coordinate : V c t w
  coordinate_ne : coordinate≠0
  ratios : Fin 3 → (V c t w)ˣ
  root_equation : ∀ j,(ratios j : V c t w)^2=Polynomial.eval coordinate (coefficients c t w D j)
  reciprocal : algebraMap (V c t w) (K c t)
    (Polynomial.eval coordinate (OddInfinitySmoothChart318.reciprocal (V c t w) D.pi D.unit))=(t : K c t)⁻¹
  original_zero : D.multiplier 0*(t : K c t)*
    algebraMap (V c t w) (K c t) (D.pi*coordinate)=roots c t 0
  original_others : ∀ j : Fin 3,D.multiplier j.succ*(t : K c t)*
    algebraMap (V c t w) (K c t) (D.pi*coordinate*(ratios j : V c t w))=roots c t j.succ

@[expose] def point (C : Center c t w D) : Ring c t w D →+* V c t w :=
  ThreePolynomialEtaleChart318.point (V c t w) (coefficients c t w D)
    C.coordinate C.ratios C.root_equation

theorem point_scalar (C : Center c t w D) (k : V c t w) :
    point c t w D C (algebraMap (V c t w) (Ring c t w D) k)=k :=
  ThreePolynomialEtaleChart318.point_scalar _ _ _ _ _ _
theorem smooth (h2 : IsUnit (2 : V c t w)) : Algebra.Smooth (V c t w) (Ring c t w D) :=
  ThreePolynomialEtaleChart318.smooth _ _ h2

theorem exists_center (ht : ¬w (t : K c t)≤1) (hodd : ∀ i,D.exponent i=1) :
    Nonempty (Center c t w D) := by
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
  have hrel' (i : Fin 4) : (z i)^2=(D.unit i : V c t w)*D.pi*T*
      (1-IntegralSourceBranches318.contacts (V c t w) i*T) := by
    simpa [Data.coefficients,hodd i] using hrel i
  obtain ⟨Z,r,hZ,hz0,hwZ,hzr,hr2⟩ := OddInfinityIntegralCoordinates318.exists_coordinates
    (V c t w) (K c t) D.pi D.irreducible D.unit
    (IntegralSourceBranches318.contacts (V c t w)) rfl T hT0 hTn z hrel'
  have hpoly : Polynomial.eval Z
      (OddInfinitySmoothChart318.reciprocal (V c t w) D.pi D.unit)=T := by
    simpa only [OddInfinitySmoothChart318.reciprocal,eval_mul,eval_C,eval_pow,eval_X] using hwZ.symm
  refine ⟨⟨Z,hZ,r,?_,?_,?_,?_⟩⟩
  · intro j
    simp only [coefficients,OddInfinitySmoothChart318.coefficient,eval_mul,eval_C,eval_sub,
      eval_one,hpoly]
    exact hr2 j
  · rw [hpoly,hT]
  · rw [←hz0]
    exact hr 0
  · intro j
    rw [←hzr j]
    exact hr j.succ

/-- The parity split needed by the local models is PRODUCED from the
same original point. In the second branch the actual infinity point,
all signed roots, and a smooth odd-place chart are already constructed. -/
theorem even_or_center (ht : ¬w (t : K c t)≤1) :
    (∀ i,D.exponent i=0) ∨ Nonempty (Center c t w D) := by
  rcases OriginalReciprocalParity318.even_or_odd c t w D ht with he|ho
  · exact Or.inl he
  · exact Or.inr (exists_center c t w D ht ho)
end OriginalOddReciprocalCenter318
