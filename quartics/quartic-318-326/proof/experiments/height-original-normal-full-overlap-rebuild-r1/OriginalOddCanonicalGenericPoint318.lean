module
public import OriginalOddCanonicalCenter318
public section
noncomputable section
namespace OriginalOddCanonicalGenericPoint318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OddInfinityWholeModelMap318 OddInfinityCanonicalCoefficients318
open OriginalOddCanonicalCenter318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  (P : OriginalOddReciprocalCenter318.Center c t w D)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "C" => OriginalOddReciprocalCenter318.Ring c t w D
local notation "B" => OddInfinityGenericCanonical318.Generic V D.pi D.unit a

@[expose] def evaluation : C →ₐ[V] K c t where
  toRingHom := (algebraMap V (K c t)).comp (OriginalOddReciprocalCenter318.point c t w D P)
  commutes' r := by
    change algebraMap V (K c t) (OriginalOddReciprocalCenter318.point c t w D P
      (algebraMap V C r))=algebraMap V (K c t) r
    rw [OriginalOddReciprocalCenter318.point_scalar]
lemma evaluation_z : evaluation c t w D P (z V D.pi D.unit a)=
    algebraMap V (K c t) P.coordinate := by
  change algebraMap V (K c t) (OriginalOddReciprocalCenter318.point c t w D P _) = _
  rw [point_z]

/-- The SAME original generic point really lies on the different-unit
open. Thus its comparison is not a statement on an uninhabited open. -/
lemma different_ne : evaluation c t w D P (different V D.pi D.unit a)≠0 := by
  have hp : algebraMap V (K c t) D.pi≠0 := by
    simpa only [map_zero] using (IsFractionRing.injective V (K c t)).ne D.irreducible.ne_zero
  have hz : algebraMap V (K c t) P.coordinate≠0 := by
    simpa only [map_zero] using (IsFractionRing.injective V (K c t)).ne P.coordinate_ne
  have hr : evaluation c t w D P (ratioProductUnit V D.pi D.unit a:C)≠0 :=
    ((ratioProductUnit V D.pi D.unit a).isUnit.map (evaluation c t w D P)).ne_zero
  rw [different_eq]
  simp only [map_mul,map_pow,map_ofNat,AlgHom.commutes,evaluation_z]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hp))
    (pow_ne_zero 4 hz)) hr

@[expose] def genericPoint : B →ₐ[V] K c t :=
  IsLocalization.Away.liftAlgHom (f:=evaluation c t w D P) (different V D.pi D.unit a)
    (IsUnit.mk0 _ (different_ne c t w D P))
lemma genericPoint_base (x : C) : genericPoint c t w D P (algebraMap C B x)=
    evaluation c t w D P x :=
  IsLocalization.Away.lift_eq _ _ x

/-- Literal equality of whole original order maps, retaining every
coefficient and all four signed roots, not just their squares. -/
theorem whole_source (hodd : ∀ i,D.exponent i=1) :
    (genericPoint c t w D P).toRingHom.comp
      (OddInfinityGenericCanonical318.genericSource V D.pi D.unit D.coefficients a rfl
        (coefficients_odd c t w D hodd))=
    (algebraMap V (K c t)).comp (modelPoint c t w D hodd P) := by
  ext x
  change genericPoint c t w D P (algebraMap C B
    (sourceMap V D.pi D.unit D.coefficients a rfl (coefficients_odd c t w D hodd) x))=_
  rw [genericPoint_base]
  rfl
end OriginalOddCanonicalGenericPoint318
