module

public import SelectedActualMarkedCuspPunctureEvaluation318
public import SelectedActualMarkedPunctureSeparation318

public section
noncomputable section

open AlgebraicGeometry Filter
open scoped Topology Polynomial
open FiniteCuspEnds318 GammaOneAtlas318
open SelectedComplexOrdinaryBase318
open SelectedActualComplexWholeRootField318 (Period periodMap)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedCuspPunctureEvaluation318
open SelectedActualMarkedPunctureSeparation318
open OpenJComplexEvaluation318 (Admissible)

namespace SelectedActualMarkedCuspPunctureSeparation318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N : ℕ) [NeZero N]
variable (p : (OpenJModel318.Base N)[X])

/-- The literal base coordinate in the same original monic ring. -/
abbrev jSection : OrdinaryRoot N p :=
  AdjoinRoot.of (pC N p) (algebraMap ℂ[X] Base Polynomial.X)

/-- The literal marked abscissa in the same original monic ring. -/
abbrev markedXSection : OrdinaryRoot N p := AdjoinRoot.root (pC N p)

variable (hN : 5 ≤ N) (hRoots : fullRootSet N p) (t : Period)

private theorem cusp_j_section_value (z : AllCuspOverlap318.Punctures N hN)
    (h : Admissible (originalCuspLift N hN z.1 z.2)) :
    atCusp N hN z.1 p hRoots t z.2 (jSection N p) =
      ActualQJ318.jInvariant (originalCuspLift N hN z.1 z.2) := by
  let u : Period := ⟨originalCuspLift N hN z.1 z.2,h⟩
  have he := RingHom.congr_fun
    (atCusp_of_ordinary_lift N hN z.1 p hRoots t z.2 u
      (originalCuspLift_projection N hN z.1 z.2)) (jSection N p)
  have hb := atPeriod_base N p hRoots u (algebraMap ℂ[X] Base Polynomial.X)
  have hv := (evaluation_polynomial (periodMap N u).1 Polynomial.X).trans Polynomial.eval_X
  exact he.trans (hb.trans hv)

private theorem cusp_x_section_value (z : AllCuspOverlap318.Punctures N hN)
    (h : Admissible (originalCuspLift N hN z.1 z.2)) :
    atCusp N hN z.1 p hRoots t z.2 (markedXSection N p) =
      SelectedMarkedPeriodCoordinate318.arithmeticX N (originalCuspLift N hN z.1 z.2) := by
  let u : Period := ⟨originalCuspLift N hN z.1 z.2,h⟩
  have he := RingHom.congr_fun
    (atCusp_of_ordinary_lift N hN z.1 p hRoots t z.2 u
      (originalCuspLift_projection N hN z.1 z.2)) (markedXSection N p)
  exact he.trans (atPeriod_root N p hRoots u)

/-- The original J and marked abscissa separate the actual punctured
width charts, even if their end indices have not yet been identified. -/
theorem actual_cusp_punctures_eq_of_literal_generator_values
    (z w : AllCuspOverlap318.Punctures N hN)
    (hz : Admissible (originalCuspLift N hN z.1 z.2))
    (hw : Admissible (originalCuspLift N hN w.1 w.2))
    (hJ : atCusp N hN z.1 p hRoots t z.2 (jSection N p) =
          atCusp N hN w.1 p hRoots t w.2 (jSection N p))
    (hX : atCusp N hN z.1 p hRoots t z.2 (markedXSection N p) =
          atCusp N hN w.1 p hRoots t w.2 (markedXSection N p)) :
    z = w := by
  have hj := (cusp_j_section_value N p hN hRoots t z hz).symm.trans
    (hJ.trans (cusp_j_section_value N p hN hRoots t w hw))
  have hx := (cusp_x_section_value N p hN hRoots t z hz).symm.trans
    (hX.trans (cusp_x_section_value N p hN hRoots t w hw))
  have h := quotient_eq_of_marked_coordinates_eq N (by omega)
    (originalCuspLift N hN z.1 z.2) (originalCuspLift N hN w.1 w.2) hz hw hj hx
  have hi := (originalCuspLift_projection N hN z.1 z.2).symm.trans
    (h.trans (originalCuspLift_projection N hN w.1 w.2))
  have hOld (v : AllCuspOverlap318.Punctures N hN) :
      cuspInverse N hN v.1 v.2 = AllCuspOverlap318.oldMap N hN v := by
    rcases v with ⟨e,a⟩
    exact RotatedPartialChart318.inverseFunction_coe N hN (representative N e) a
  exact AllCuspOverlap318.oldMap_injective N hN ((hOld z).symm.trans (hi.trans (hOld w)))

/-- A motion on the actual punctured width coordinate cannot preserve
both original functions while moving every sufficiently small point. -/
theorem no_moving_symmetry_of_literal_cusp_generators
    (c : End N) (σ : ℂ → ℂ)
    (hσ : Tendsto σ (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)))
    (hmove : ∀ᶠ q in 𝓝[≠] (0 : ℂ), σ q ≠ q)
    (hJ : (fun q => atCusp N hN c p hRoots t (σ q) (jSection N p)) =ᶠ[𝓝[≠] (0 : ℂ)]
       fun q => atCusp N hN c p hRoots t q (jSection N p))
    (hX : (fun q => atCusp N hN c p hRoots t (σ q) (markedXSection N p)) =ᶠ[𝓝[≠] (0 : ℂ)]
       fun q => atCusp N hN c p hRoots t q (markedXSection N p)) : False := by
  have ha := eventually_ordinary_at_original_cusp N hN c
  have hf : ∀ᶠ q in 𝓝[≠] (0 : ℂ), False := by
    filter_upwards [hσ.eventually ha,ha,hmove,hJ,hX] with q hs hq hm hj hx
    let z : AllCuspOverlap318.Punctures N hN := ⟨c,⟨σ q,hs.1⟩⟩
    let w : AllCuspOverlap318.Punctures N hN := ⟨c,⟨q,hq.1⟩⟩
    have he := actual_cusp_punctures_eq_of_literal_generator_values N p hN hRoots t
      z w hs.2 hq.2 hj hx
    exact hm (congrArg (fun v : AllCuspOverlap318.Punctures N hN => (v.2 : ℂ)) he)
  exact (Filter.NeBot.ne inferInstance) (Filter.eventually_false_iff_eq_bot.mp hf)

end SelectedActualMarkedCuspPunctureSeparation318

#print axioms SelectedActualMarkedCuspPunctureSeparation318.actual_cusp_punctures_eq_of_literal_generator_values
#print axioms SelectedActualMarkedCuspPunctureSeparation318.no_moving_symmetry_of_literal_cusp_generators
