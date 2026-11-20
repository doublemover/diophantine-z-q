module
public import SelectedShortOrdinaryScale318
public section
noncomputable section
open Polynomial WeierstrassCurve
open SelectedShortOrdinaryRatio318 SelectedShortOrdinaryScale318 EvenContactEtale318

namespace SelectedShortScaleTest318
variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable (W V : WeierstrassCurve R) [W.IsShortNF] [V.IsShortNF] [W.IsElliptic] [V.IsElliptic]
variable (hW0 : IsUnit W.j) (hW1 : IsUnit (W.j-1728))
variable (hV0 : IsUnit V.j) (hV1 : IsUnit (V.j-1728))
variable (u : Tˣ)

abbrev scaleCondition : Prop :=
  algebraMap R T V.a₄ = (u:T)^4*algebraMap R T W.a₄ ∧
    algebraMap R T V.a₆ = (u:T)^6*algebraMap R T W.a₆

/-- The exact equation for every compatible scale over any test ring.
No splitting assertion about an arbitrary test ring is used. -/
theorem scale_iff_square (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : W.j = V.j) :
    scaleCondition W V u ↔ (u:T)^2 = algebraMap R T (c W V hW0 hW1 hV0 hV1:R) := by
  let d := c W V hW0 hW1 hV0 hV1
  let a := ratio4 W V hW0 hV0
  let b := ratio6 W V hW1 hV1
  have ha : d^2 = a := ratio_sq W V hW0 hW1 hV0 hV1 h2 h3 hj
  have hb : d^3 = b := ratio_cube W V hW0 hW1 hV0 hV1 h2 h3 hj
  have hab : d*a=b := by rw [← ha,← hb]; group
  have haV : (a:R)*W.a₄=V.a₄ := ratio4_mul W V hW0 hV0
  have hbV : (b:R)*W.a₆=V.a₆ := ratio6_mul W V hW1 hV1
  constructor
  · intro uv
    have ua : (u:T)^4 = algebraMap R T (a:R) := by
      apply ((coeff4_unit W hW0).map (algebraMap R T)).mul_right_cancel
      rw [← map_mul,haV]
      exact uv.1.symm
    have ub : (u:T)^6 = algebraMap R T (b:R) := by
      apply ((coeff6_unit W hW1).map (algebraMap R T)).mul_right_cancel
      rw [← map_mul,hbV]
      exact uv.2.symm
    apply (a.isUnit.map (algebraMap R T)).mul_right_cancel
    calc
      (u:T)^2 * algebraMap R T (a:R) = (u:T)^6 := by rw [← ua]; ring
      _ = algebraMap R T (b:R) := ub
      _ = algebraMap R T (d:R) * algebraMap R T (a:R) := by
        rw [← map_mul]
        exact congrArg (fun w : Rˣ => algebraMap R T (w:R)) hab.symm
  · intro hu
    have ha' : (u:T)^4 = algebraMap R T (a:R) := by
      calc
        _ = ((u:T)^2)^2 := by ring
        _ = _ := by
          rw [hu,← map_pow]
          exact congrArg (fun w : Rˣ => algebraMap R T (w:R)) ha
    have hb' : (u:T)^6 = algebraMap R T (b:R) := by
      calc
        _ = ((u:T)^2)^3 := by ring
        _ = _ := by
          rw [hu,← map_pow]
          exact congrArg (fun w : Rˣ => algebraMap R T (w:R)) hb
    constructor
    · rw [ha',← map_mul,haV]
    · rw [hb',← map_mul,hbV]

/-- The universal root algebra map of the actual ratio produces the
given compatible short-model coordinate scale, not an independently
chosen root. -/
theorem factor_scale (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : W.j = V.j)
    (hu : scaleCondition W V u) :
    ∃! f : Cover W V hW0 hW1 hV0 hV1 →ₐ[R] T,
      f (r W V hW0 hW1 hV0 hV1) = (u:T) := by
  let d := c W V hW0 hW1 hV0 hV1
  have hd : (u:T)^2 = algebraMap R T (d:R) :=
    (scale_iff_square W V hW0 hW1 hV0 hV1 u h2 h3 hj).mp hu
  have hp : aeval (u:T) (polynomial d) = 0 := by
    simp only [polynomial,map_sub,map_pow,aeval_X,aeval_C,hd,sub_self]
  let f : RootRing d →ₐ[R] T :=
    AdjoinRoot.liftAlgHom (polynomial d) (Algebra.ofId R T) (u:T) hp
  have hf : f (root d) = (u:T) := AdjoinRoot.liftAlgHom_root _ _ _ _
  refine ⟨f,hf,?_⟩
  intro g hg
  apply AdjoinRoot.algHom_ext
  exact hg.trans hf.symm

end SelectedShortScaleTest318

#print axioms SelectedShortScaleTest318.scale_iff_square
#print axioms SelectedShortScaleTest318.factor_scale
