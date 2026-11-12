module
public import OriginalAllPlaceRootBounds318
public import IntegralZoomNeighborhood318
public section
noncomputable section
namespace OriginalAllPrimeZoomInput318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 Polynomial
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
inductive Mode | finite | reciprocal
@[expose] def alpha : Mode → Fin 4 → V c t w
  | .finite => fun _ => 0
  | .reciprocal => fun i => -D.coefficients i*IntegralSourceBranches318.contacts (V c t w) i
@[expose] def beta : Fin 4 → V c t w := D.coefficients
@[expose] def gamma : Mode → Fin 4 → V c t w
  | .finite => fun i => -D.coefficients i*IntegralSourceBranches318.contacts (V c t w) i
  | .reciprocal => fun _ => 0
@[expose] def originalCoefficients : Mode → Fin 4 → (V c t w)[X]
  | .finite => DVRNormalizedFiniteOrder318.coefficient (V c t w) D.coefficients
      (IntegralSourceBranches318.contacts (V c t w))
  | .reciprocal => DVRNormalizedInfinityOrder318.coefficient (V c t w) D.coefficients
      (IntegralSourceBranches318.contacts (V c t w))
@[expose] def fieldCoordinate : Mode → K c t
  | .finite => (t : K c t)
  | .reciprocal => (t : K c t)⁻¹
@[expose] def fieldRoot : Mode → Fin 4 → K c t
  | .finite => D.normalizedRoots
  | .reciprocal => fun i => roots c t i/(D.multiplier i*(t : K c t))

/-- Literal finite or reciprocal coordinates of the SAME original point.
The roots are specified by equality to their original signed values. -/
structure Input (m : Mode) where
  coordinate : V c t w
  root : Fin 4 → V c t w
  coordinate_value : algebraMap (V c t w) (K c t) coordinate=fieldCoordinate c t m
  root_value : ∀ i,algebraMap (V c t w) (K c t) (root i)=fieldRoot c t w D m i
  root_equation : ∀ i,(root i)^2=IntegralQuadraticPointZoom318.value
    (alpha c t w D m) (beta c t w D) (gamma c t w D m) coordinate i
  root_ne : ∀ i,root i≠0

theorem coefficient_identity (m : Mode) : originalCoefficients c t w D m=
    IntegralZoomNeighborhood318.oldCoefficient (V c t w)
      (alpha c t w D m) (beta c t w D) (gamma c t w D m) := by
  funext i
  cases m <;> simp only [originalCoefficients,DVRNormalizedFiniteOrder318.coefficient,
    DVRNormalizedInfinityOrder318.coefficient,IntegralZoomNeighborhood318.oldCoefficient,
    alpha,beta,gamma,map_neg,map_mul,map_zero] <;> ring

/-- The noncontact hypothesis constructs an integral zoom input at EVERY
finite place, including characteristic2 and every collision prime. -/
theorem exists_input (hn : ∀ i,RationalContactPoint318.parameters c t i≠0) :
    ∃ m : Mode,Nonempty (Input c t w D m) := by
  have hroot (i : Fin 4) : roots c t i≠0 :=
    RationalFourRootFiber318.root_ne_zero _ i (hn i)
  by_cases ht : w (t : K c t)≤1
  · obtain ⟨T,r,hT,hr,hrel⟩ := OriginalAllPlaceRootBounds318.finite_coordinates c t w D ht
    refine ⟨.finite,⟨⟨T,r,hT,hr,?_,?_⟩⟩⟩
    · intro i
      rw [hrel i]
      simp only [IntegralQuadraticPointZoom318.value,alpha,beta,gamma,zero_mul,zero_add]
      ring
    · intro i hi
      have h := hr i
      rw [hi,map_zero] at h
      exact (div_ne_zero (hroot i) (D.multiplier_ne i)) h.symm
  · obtain ⟨T,r,ht0,hT,hr,hrel,hrecover⟩ := OriginalAllPlaceRootBounds318.reciprocal_coordinates c t w D ht
    refine ⟨.reciprocal,⟨⟨T,r,hT,hr,?_,?_⟩⟩⟩
    · intro i
      rw [hrel i]
      simp only [IntegralQuadraticPointZoom318.value,alpha,beta,gamma,add_zero]
      ring
    · intro i hi
      have h := hr i
      rw [hi,map_zero] at h
      exact (div_ne_zero (hroot i) (mul_ne_zero (D.multiplier_ne i) ht0)) h.symm

namespace Input
variable {m : Mode} (I : Input c t w D m)
abbrev Chart := IntegralZoomNeighborhood318.Chart (V c t w)
  (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate
@[expose] def point : I.Chart →+* V c t w := IntegralZoomNeighborhood318.point (V c t w)
  (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate

theorem smooth : Algebra.Smooth (V c t w) I.Chart := IntegralZoomNeighborhood318.smooth _ _ _ _ _

theorem scale_ne : IntegralQuadraticPointZoom318.scale
    (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate≠0 := by
  apply mul_ne_zero (by norm_num : (4 : V c t w)≠0)
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [←I.root_equation i]
  exact pow_ne_zero _ (I.root_ne i)

/-- Full actual original-order map. Its scalar action is the literal
old contact coordinate inside the newly constructed smooth chart. -/
@[expose] def sourceMap : FourRootOrder318.Order (originalCoefficients c t w D m) →+* I.Chart := by
  letI : Algebra (V c t w)[X] I.Chart :=
    (IntegralZoomNeighborhood318.oldScalar (V c t w)
      (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate).toAlgebra
  refine (IntegralRootPointMaps318.fourMap (originalCoefficients c t w D m)
    (IntegralZoomNeighborhood318.oldRoot (V c t w)
      (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate I.root) ?_).toRingHom
  intro i
  rw [coefficient_identity]
  exact IntegralZoomNeighborhood318.original_root_equation (V c t w)
    (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate I.root I.root_equation i

/-- The all-prime construction recovers the specified original signed
root values, not merely their squares or the original coordinate ratio. -/
theorem original_root_value (i : Fin 4) :
    algebraMap (V c t w) (K c t)
      (I.point (IntegralZoomNeighborhood318.oldRoot (V c t w)
        (alpha c t w D m) (beta c t w D) (gamma c t w D m) I.coordinate I.root i))=
      fieldRoot c t w D m i := by
  rw [point,IntegralZoomNeighborhood318.point_oldRoot]
  exact I.root_value i
end Input
end OriginalAllPrimeZoomInput318
