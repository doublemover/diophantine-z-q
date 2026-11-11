module
public import OddInfinityGlobalCanonicalSections318
public import OriginalOddReciprocalCenter318
public section
noncomputable section
namespace OriginalOddCanonicalCenter318
open NumberField AlgebraicGeometry CategoryTheory Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OddInfinityWholeModelMap318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "C" => OriginalOddReciprocalCenter318.Ring c t w D
variable (hodd : ∀ i,D.exponent i=1)
include hodd in
lemma coefficients_odd (i : Fin 4) : D.coefficients i=(D.unit i:V)*D.pi := by
  simp [Data.coefficients,hodd i]

@[expose] def modelMap : DVRNormalizedInfinityOrder318.Order V D.coefficients a →+* C :=
  sourceMap V D.pi D.unit D.coefficients a rfl (coefficients_odd c t w D hodd)
variable (P : OriginalOddReciprocalCenter318.Center c t w D)
@[expose] def reciprocalCoordinate : V :=
  Polynomial.eval P.coordinate (OddInfinitySmoothChart318.reciprocal V D.pi D.unit)
@[expose] def modelPoint : DVRNormalizedInfinityOrder318.Order V D.coefficients a →+* V :=
  (OriginalOddReciprocalCenter318.point c t w D P).comp (modelMap c t w D hodd)

lemma point_s : OriginalOddReciprocalCenter318.point c t w D P (s V D.pi D.unit a)=
    reciprocalCoordinate c t w D P :=
  ThreePolynomialEtaleChart318.point_polynomial _ _ _ _ _ _
lemma point_z : OriginalOddReciprocalCenter318.point c t w D P (z V D.pi D.unit a)=P.coordinate :=
  ThreePolynomialEtaleChart318.point_coordinate _ _ _ _ _
lemma point_ratio (j : Fin 3) : OriginalOddReciprocalCenter318.point c t w D P
    (ratio V D.pi D.unit a j)=(P.ratios j:V) :=
  ThreePolynomialEtaleChart318.point_root _ _ _ _ _ _

lemma point_scalarMap : (OriginalOddReciprocalCenter318.point c t w D P).comp
    (scalarMap V D.pi D.unit a)=Polynomial.evalRingHom (reciprocalCoordinate c t w D P) := by
  apply Polynomial.ringHom_ext
  · intro v
    simp only [RingHom.comp_apply,scalarMap,coe_eval₂RingHom,eval₂_C,
      OriginalOddReciprocalCenter318.point_scalar,Polynomial.evalRingHom_apply,eval_C]
  · simp only [RingHom.comp_apply,scalarMap,coe_eval₂RingHom,eval₂_X,
      Polynomial.evalRingHom_apply,eval_X]
    exact point_s c t w D P

lemma modelPoint_polynomial (p : V[X]) : modelPoint c t w D hodd P
    (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V D.coefficients a) p)=
      Polynomial.eval (reciprocalCoordinate c t w D P) p := by
  change OriginalOddReciprocalCenter318.point c t w D P (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_polynomial]
  exact RingHom.congr_fun (point_scalarMap c t w D P) p

lemma modelPoint_signed (i : Fin 4) : D.multiplier i*(t:K c t)*algebraMap V (K c t)
    (modelPoint c t w D hodd P (FourRootOrderSigns318.generator
      (DVRNormalizedInfinityOrder318.coefficient V D.coefficients a) i))=roots c t i := by
  change D.multiplier i*(t:K c t)*algebraMap V (K c t)
    (OriginalOddReciprocalCenter318.point c t w D P (sourceMap _ _ _ _ _ _ _ _))=_
  rw [sourceMap_root]
  refine Fin.cases ?_ (fun j => ?_) i
  · change D.multiplier 0*(t:K c t)*algebraMap V (K c t)
      (OriginalOddReciprocalCenter318.point c t w D P (algebraMap V C D.pi*z V D.pi D.unit a))=_
    rw [map_mul,OriginalOddReciprocalCenter318.point_scalar,point_z]
    exact P.original_zero
  · change D.multiplier j.succ*(t:K c t)*algebraMap V (K c t)
      (OriginalOddReciprocalCenter318.point c t w D P
        (algebraMap V C D.pi*z V D.pi D.unit a*ratio V D.pi D.unit a j))=_
    rw [map_mul,map_mul,OriginalOddReciprocalCenter318.point_scalar,point_z,point_ratio]
    exact P.original_others j

/-- Equality of the entire specified generic SCHEME point on the same
whole proper model. It retains every signed root and the base map. -/
theorem generic_extension (ht : (t:K c t)≠0) :
    Spec.map (CommRingCat.ofHom (algebraMap V (K c t))) ≫
      (Spec.map (CommRingCat.ofHom (modelPoint c t w D hodd P)) ≫
        NormalizedWholeOpenMaps318.infinityChart V D.coefficients a)=D.genericPoint := by
  apply NormalizedGenericPointExtension318.infinity_extension V (K c t)
    D.coefficients a (t:K c t) D.normalizedRoots D.root_equation ht
    (reciprocalCoordinate c t w D P) P.reciprocal
    (modelPoint c t w D hodd P) (modelPoint_polynomial c t w D hodd P)
  intro i
  change _ = (roots c t i/D.multiplier i)/(t:K c t)
  apply (eq_div_iff ht).2
  apply (eq_div_iff (D.multiplier_ne i)).2
  simpa only [mul_comm,mul_left_comm,mul_assoc] using modelPoint_signed c t w D hodd P i
end OriginalOddCanonicalCenter318
