module
public import SelectedShortOrdinaryRatio318
public import EvenContactCover318
public import OpenJModel318
public section
noncomputable section
open WeierstrassCurve AlgebraicGeometry CategoryTheory
open SelectedShortOrdinaryRatio318 EvenContactEtale318

namespace SelectedShortOrdinaryScale318
variable {R : Type*} [CommRing R]

/-- This is the actual change of Weierstrass variables with affine point
coordinates (x,y) sent to (r²x,r³y): Lean's stored u is r⁻¹. -/
@[expose] def pureChange (r : Rˣ) : WeierstrassCurve.VariableChange R :=
  ⟨r⁻¹,0,0,0⟩

theorem pureChange_of_coeffs (W V : WeierstrassCurve R) [W.IsShortNF] [V.IsShortNF]
    (r : Rˣ) (h4 : V.a₄ = (r:R)^4*W.a₄) (h6 : V.a₆ = (r:R)^6*W.a₆) :
    pureChange r • W = V := by
  ext <;> simp [pureChange,variableChange_a₁,variableChange_a₂,variableChange_a₃,
    variableChange_a₄,variableChange_a₆,a₁_of_isShortNF,a₂_of_isShortNF,a₃_of_isShortNF,h4,h6]

theorem map_short (W : WeierstrassCurve R) [W.IsShortNF]
    {T : Type*} [CommRing T] (f : R →+* T) : (W.map f).IsShortNF := by
  constructor
  · change f W.a₁ = 0
    rw [a₁_of_isShortNF,map_zero]
  · change f W.a₂ = 0
    rw [a₂_of_isShortNF,map_zero]
  · change f W.a₃ = 0
    rw [a₃_of_isShortNF,map_zero]

variable (W V : WeierstrassCurve R) [W.IsShortNF] [V.IsShortNF] [W.IsElliptic] [V.IsElliptic]
variable (hW0 : IsUnit W.j) (hW1 : IsUnit (W.j-1728))
variable (hV0 : IsUnit V.j) (hV1 : IsUnit (V.j-1728))

abbrev c := ratio W V hW0 hW1 hV0 hV1
abbrev Cover := RootRing (c W V hW0 hW1 hV0 hV1)
abbrev r := root (c W V hW0 hW1 hV0 hV1)

/-- The cover is the genuine finite étale spectrum of the ratio-root
algebra and is surjective on every nonempty affine test base. -/
theorem cover_over_base [Nontrivial R] (h2 : IsUnit (2:R)) :
    IsFinite (EvenContactCover318.structureMap (c W V hW0 hW1 hV0 hV1)) ∧
    Etale (EvenContactCover318.structureMap (c W V hW0 hW1 hV0 hV1)) ∧
    Surjective (EvenContactCover318.structureMap (c W V hW0 hW1 hV0 hV1)) :=
  ⟨(EvenContactCover318.finite_etale _ h2).1,
    (EvenContactCover318.finite_etale _ h2).2,(EvenContactCover318.flat_surjective _).2⟩

@[expose] def rootUnit : (Cover W V hW0 hW1 hV0 hV1)ˣ :=
  (root_isUnit _).unit

@[simp] theorem rootUnit_val :
    (rootUnit W V hW0 hW1 hV0 hV1 : Cover W V hW0 hW1 hV0 hV1) = r W V hW0 hW1 hV0 hV1 :=
  (root_isUnit _).unit_spec

section Powers
variable (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : W.j = V.j)

include h2 h3 hj in
theorem fourth_power :
    (r W V hW0 hW1 hV0 hV1)^4 =
      algebraMap R (Cover W V hW0 hW1 hV0 hV1) (ratio4 W V hW0 hV0:R) := by
  let z := r W V hW0 hW1 hV0 hV1
  calc
    _ = (z^2)^2 := by change z^4 = (z^2)^2; ring
    _ = _ := by
      change (root (c W V hW0 hW1 hV0 hV1)^2)^2 = _
      rw [root_square,← map_pow]
      exact congrArg (fun u : Rˣ => algebraMap R (Cover W V hW0 hW1 hV0 hV1) (u:R))
        (ratio_sq W V hW0 hW1 hV0 hV1 h2 h3 hj)

include h2 h3 hj in
theorem sixth_power :
    (r W V hW0 hW1 hV0 hV1)^6 =
      algebraMap R (Cover W V hW0 hW1 hV0 hV1) (ratio6 W V hW1 hV1:R) := by
  let z := r W V hW0 hW1 hV0 hV1
  calc
    _ = (z^2)^3 := by change z^6 = (z^2)^3; ring
    _ = _ := by
      change (root (c W V hW0 hW1 hV0 hV1)^2)^3 = _
      rw [root_square,← map_pow]
      exact congrArg (fun u : Rˣ => algebraMap R (Cover W V hW0 hW1 hV0 hV1) (u:R))
        (ratio_cube W V hW0 hW1 hV0 hV1 h2 h3 hj)

include h2 h3 hj in
/-- The exact two actual Weierstrass models are isomorphic by the
specific root scale, as a genuine equality under variable change. -/
theorem change_on_cover :
    pureChange (rootUnit W V hW0 hW1 hV0 hV1) •
        W.map (algebraMap R (Cover W V hW0 hW1 hV0 hV1)) =
      V.map (algebraMap R (Cover W V hW0 hW1 hV0 hV1)) := by
  let B := Cover W V hW0 hW1 hV0 hV1
  letI : (W.map (algebraMap R B)).IsShortNF := map_short W _
  letI : (V.map (algebraMap R B)).IsShortNF := map_short V _
  apply pureChange_of_coeffs
  · change algebraMap R B V.a₄ =
      (rootUnit W V hW0 hW1 hV0 hV1:B)^4 * algebraMap R B W.a₄
    rw [rootUnit_val,fourth_power W V hW0 hW1 hV0 hV1 h2 h3 hj,← map_mul,ratio4_mul]
  · change algebraMap R B V.a₆ =
      (rootUnit W V hW0 hW1 hV0 hV1:B)^6 * algebraMap R B W.a₆
    rw [rootUnit_val,sixth_power W V hW0 hW1 hV0 hV1 h2 h3 hj,← map_mul,ratio6_mul]

end Powers

section Literal
variable (N : ℕ) (f : OpenJModel318.Base N →+* R)

abbrev literal := (OpenJModel318.integralModel N).map f
instance literal_short : (literal N f).IsShortNF := by
  letI : (OpenJModel318.integralModel N).IsShortNF := ⟨rfl,rfl,rfl⟩
  exact map_short (OpenJModel318.integralModel N) f
instance literal_elliptic : (literal N f).IsElliptic := OpenJModel318.base_change_elliptic N f

theorem literal_j_units :
    IsUnit (literal N f).j ∧ IsUnit ((literal N f).j-1728) := by
  rw [OpenJModel318.base_change_j]
  refine ⟨(OpenJModel318.base_units N).2.2.2.1.map f,?_⟩
  simpa only [map_sub,map_ofNat] using (OpenJModel318.base_units N).2.2.2.2.map f

/-- Literal chart version, with all four coefficient-unit hypotheses
derived from the original localization and from its exact j equality. -/
theorem literal_ord_cover (V : WeierstrassCurve R) [V.IsShortNF] [V.IsElliptic]
    (hj : V.j = f (OpenJModel318.jCoord N)) :
    ∃ u : Rˣ,
      Module.Finite R (RootRing u) ∧ Algebra.Etale R (RootRing u) ∧
      pureChange (root_isUnit u).unit •
        (literal N f).map (algebraMap R (RootRing u)) =
        V.map (algebraMap R (RootRing u)) := by
  have h : (literal N f).j = V.j := (OpenJModel318.base_change_j N f).trans hj.symm
  obtain ⟨h0,h1⟩ := literal_j_units N f
  have v0 : IsUnit V.j := by rwa [← h]
  have v1 : IsUnit (V.j-1728) := by rwa [← h]
  have h2 : IsUnit (2:R) := by simpa only [map_ofNat] using (OpenJModel318.base_units N).1.map f
  have h3 : IsUnit (3:R) := by simpa only [map_ofNat] using (OpenJModel318.base_units N).2.1.map f
  let u := c (literal N f) V h0 h1 v0 v1
  exact ⟨u,rootRing_finite u,rootRing_etale u h2,
    change_on_cover (literal N f) V h0 h1 v0 v1 h2 h3 h⟩

end Literal
end SelectedShortOrdinaryScale318

#print axioms SelectedShortOrdinaryScale318.change_on_cover
#print axioms SelectedShortOrdinaryScale318.literal_ord_cover
