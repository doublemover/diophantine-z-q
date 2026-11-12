module
public import PELOriginalFixedIntegralCoordinates318
public import PELFixedNormalizerFiniteSearch318
public import PELDirichletOrbitBound318
public section
noncomputable section
namespace PELOriginalFixedPolygonSearch318
open PELPrincipalOrderCoordinates318 PELLevelThreeSimilitudes318
open PELIntegralEllipticObstructions318 PELQuaternionRealRepresentation318
open PELOriginalFixedKleinCoordinates318 PELOriginalFixedIntegralCoordinates318
open QuaternionicFixedParameter318 QuaternionicJointPeriodTopology318
open PELDirichletHeight318 PELDirichletOrbitBound318 PELDirichletOriginalUnits318
open PELJointNormOneAction318
set_option maxHeartbeats 2400000

lemma abs_natCast (z : ℤ) : (z.natAbs:ℝ)=|(z:ℝ)| := by
  exact_mod_cast Int.natCast_natAbs z

/-- Exhaustive search inputs are PRODUCED by the original norm equation
and actual orbit-minimizing point. No rational polygon-membership packet
or precomputed list membership is assumed by this consumer. -/
theorem original_admissible (x : Coordinates) (ht : trace x=0)
    (i : Fin 5) (hn : integralNorm x=(PELFixedNormalizerFiniteSearch318.norm i:ℤ))
    (hr : 0<rotationCoordinate x) (τ : HalfPlane)
    (hfix : fixesLine (representation (embed x)) τ)
    (hmin : ∀ u : normOneUnits,height τ≤height (u • τ)) :
    PELFixedNormalizerFiniteSearch318.admissible
      (PELFixedNormalizerFiniteSearch318.norm i) (rotationCoordinate x).toNat
        (x 0).natAbs (x 3).natAbs := by
  have hnpos : 0<integralNorm x := by
    rw [hn]; fin_cases i <;> norm_num [PELFixedNormalizerFiniteSearch318.norm]
  have hrZ : ((rotationCoordinate x).toNat:ℤ)=rotationCoordinate x :=
    Int.toNat_of_nonneg hr.le
  have hrR : ((rotationCoordinate x).toNat:ℝ)=(rotationCoordinate x:ℝ) := by exact_mod_cast hrZ
  have hrpos : 0<(rotationCoordinate x:ℝ) := by exact_mod_cast hr
  have hpR : 0≤((rotationCoordinate x).toNat:ℝ) := by positivity
  have hbound := original_fixed_bound x ht hnpos τ hfix (minimum_height_bound τ hmin)
  have he := norm_equation x ht
  have hfix' := hfix
  rw [original_matrix x ht] at hfix'
  obtain ⟨hf,hs⟩ := fixed_coordinates_mul _ _ _ τ hfix'
  have hfabs : |scaledFirst τ|*((rotationCoordinate x).toNat:ℝ)=10*((x 0).natAbs:ℝ) := by
    have hh := congrArg abs hf
    simpa only [abs_mul,abs_neg,abs_ofNat,abs_of_pos hrpos,hrR,abs_natCast] using hh
  have hsabs : |scaledSecond τ|*((rotationCoordinate x).toNat:ℝ)=((x 3).natAbs:ℝ) := by
    have hh := congrArg abs hs
    simpa only [abs_mul,abs_neg,abs_of_pos hrpos,hrR,abs_natCast] using hh
  have row (j : Fin 8) := mul_le_mul_of_nonneg_right (absolute_row τ hmin j) hpR
  have h0 := row 0
  have h1 := row 1
  have h2 := row 2
  have h3 := row 3
  have h4 := row 4
  have h5 := row 5
  have h6 := row 6
  have h7 := row 7
  norm_num [rowFirst,rowSecond,rowConstant] at h0 h1 h2 h3 h4 h5 h6 h7
  have hparZ : (rotationCoordinate x+|(x 3)|)%2=0 := by
    unfold rotationCoordinate
    rcases le_total 0 (x 3) with hp|hp
    · rw [abs_of_nonneg hp]; omega
    · rw [abs_of_nonpos hp]; omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast (show (0:ℤ)<((rotationCoordinate x).toNat:ℤ) by rwa [hrZ])
  · exact_mod_cast (show 210*((rotationCoordinate x).toNat:ℤ)^2≤
        40000*(PELFixedNormalizerFiniteSearch318.norm i:ℤ) by rwa [hrZ,←hn])
  · have hp : (((rotationCoordinate x).toNat:ℤ)+((x 3).natAbs:ℤ))%2=0 := by
      rwa [hrZ,Int.natCast_natAbs]
    exact_mod_cast hp
  · exact_mod_cast (show 105*((rotationCoordinate x).toNat:ℤ)^2=
        10*((x 0).natAbs:ℤ)^2+21*((x 3).natAbs:ℤ)^2+
          2*(PELFixedNormalizerFiniteSearch318.norm i:ℤ) by
      rw [hrZ,Int.natCast_natAbs,Int.natCast_natAbs,sq_abs,sq_abs,←hn]
      linarith [he])
  · exact_mod_cast (show 130*((x 0).natAbs:ℝ)≤420*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h0,hfabs])
  · exact_mod_cast (show 170*((x 0).natAbs:ℝ)+45*((x 3).natAbs:ℝ)≤555*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h1,hfabs,hsabs])
  · exact_mod_cast (show 430*((x 0).natAbs:ℝ)+210*((x 3).natAbs:ℝ)≤1470*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h2,hfabs,hsabs])
  · exact_mod_cast (show 10*((x 0).natAbs:ℝ)+6*((x 3).natAbs:ℝ)≤35*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h3,hfabs,hsabs])
  · exact_mod_cast (show 290*((x 0).natAbs:ℝ)+210*((x 3).natAbs:ℝ)≤1050*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h4,hfabs,hsabs])
  · exact_mod_cast (show 20*((x 0).natAbs:ℝ)+17*((x 3).natAbs:ℝ)≤75*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h5,hfabs,hsabs])
  · exact_mod_cast (show 130*((x 0).natAbs:ℝ)+165*((x 3).natAbs:ℝ)≤555*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h6,hfabs,hsabs])
  · exact_mod_cast (show 3*((x 3).natAbs:ℝ)≤5*((rotationCoordinate x).toNat:ℝ) by
      nlinarith only [h7,hsabs])

/-- The actual original matrix and original group minimum force one of
only22 unsigned triples, equivalently77 signed fixed-point representatives.
Original side and normalizer orbit identifications are a separate next step. -/
theorem original_finite_list (x : Coordinates) (ht : trace x=0)
    (i : Fin 5) (hn : integralNorm x=(PELFixedNormalizerFiniteSearch318.norm i:ℤ))
    (hr : 0<rotationCoordinate x) (τ : HalfPlane)
    (hfix : fixesLine (representation (embed x)) τ)
    (hmin : ∀ u : normOneUnits,height τ≤height (u • τ)) :
    ((rotationCoordinate x).toNat,(x 0).natAbs,(x 3).natAbs)∈
      PELFixedNormalizerFiniteSearch318.rows i :=
  PELFixedNormalizerFiniteSearch318.exhaustive i _ _ _
    (original_admissible x ht i hn hr τ hfix hmin)
end PELOriginalFixedPolygonSearch318
