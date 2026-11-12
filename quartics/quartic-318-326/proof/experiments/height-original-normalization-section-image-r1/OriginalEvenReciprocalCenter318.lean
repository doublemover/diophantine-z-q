module
public import OriginalOddReciprocalCenter318
public import EvenInfinityIntegralCoordinates318
public section
noncomputable section
namespace OriginalEvenReciprocalCenter318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open ActualFinitePlaceIntegers318 Polynomial
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
abbrev coefficients := OddInfinitySmoothChart318.coefficient V 1 D.unit a
abbrev Ring := OddInfinitySmoothChart318.ModelRing V 1 D.unit a
structure Center where
  coordinate : V
  coordinate_ne : coordinate≠0
  ratios : Fin 3 → Vˣ
  root_equation : ∀ j,(ratios j:V)^2=Polynomial.eval coordinate (coefficients c t w D j)
  reciprocal : algebraMap V (K c t)
    (Polynomial.eval coordinate (OddInfinitySmoothChart318.reciprocal V 1 D.unit))=(t:K c t)⁻¹
  original_zero : D.multiplier 0*(t:K c t)*algebraMap V (K c t) coordinate=roots c t 0
  original_others : ∀ j : Fin 3,D.multiplier j.succ*(t:K c t)*
    algebraMap V (K c t) (coordinate*(ratios j:V))=roots c t j.succ
@[expose] def point (P : Center c t w D) : Ring c t w D →+* V :=
  ThreePolynomialEtaleChart318.point V (coefficients c t w D) P.coordinate P.ratios P.root_equation
lemma point_scalar (P : Center c t w D) (r : V) :
    point c t w D P (algebraMap V (Ring c t w D) r)=r :=
  ThreePolynomialEtaleChart318.point_scalar _ _ _ _ _ _

theorem exists_center (ht : ¬w (t:K c t)≤1) (heven : ∀ i,D.exponent i=0) :
    Nonempty (Center c t w D) := by
  obtain ⟨T,z,ht0,hT,hz,hrel,hr⟩ := OriginalAllPlaceRootBounds318.reciprocal_coordinates c t w D ht
  have hT0 : T≠0 := by
    intro h
    rw [h,map_zero] at hT
    exact inv_ne_zero ht0 hT.symm
  have hTn : ¬IsUnit T := by
    rintro ⟨U,hU⟩
    have hb := integer_bound w (↑U⁻¹:V)
    rw [map_units_inv,hU,hT,inv_inv] at hb
    exact ht hb
  have hrel' (i : Fin 4) : (z i)^2=(D.unit i:V)*T*(1-a i*T) := by
    simpa [Data.coefficients,heven i] using hrel i
  obtain ⟨r,hz0,hwZ,hzr,hr2⟩ := EvenInfinityIntegralCoordinates318.exists_coordinates V (K c t)
    D.unit a rfl T hT0 hTn z hrel'
  have hpoly : Polynomial.eval (z 0) (OddInfinitySmoothChart318.reciprocal V 1 D.unit)=T := by
    simpa only [OddInfinitySmoothChart318.reciprocal,eval_mul,eval_C,eval_pow,eval_X,one_mul] using hwZ.symm
  refine ⟨⟨z 0,hz0,r,?_,?_,hr 0,?_⟩⟩
  · intro j
    simp only [coefficients,OddInfinitySmoothChart318.coefficient,eval_mul,eval_C,eval_sub,eval_one,hpoly]
    exact hr2 j
  · rw [hpoly,hT]
  · intro j
    rw [←hzr j]
    exact hr j.succ
end OriginalEvenReciprocalCenter318
