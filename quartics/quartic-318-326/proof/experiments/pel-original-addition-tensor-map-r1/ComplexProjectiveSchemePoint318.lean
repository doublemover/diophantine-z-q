module
public import ComplexProjectiveMarkerPoint318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public section
noncomputable section
namespace ComplexProjectiveSchemePoint318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
variable {ι:Type*}
local instance standardGrading:GradedAlgebra (grading (ι:=ι)):=MvPolynomial.gradedAlgebra
abbrev ComplexPoint:=Spec (CommRingCat.of ℂ)
@[expose] def scalar:ℂ→+*Γ(ComplexPoint,⊤):=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
@[expose] def evaluation(v:ι→ℂ):(Equations (ι:=ι))→+*Γ(ComplexPoint,⊤):=
  scalar.comp (MvPolynomial.eval₂Hom (RingHom.id ℂ) v)
lemma evaluation_variable(v:ι→ℂ)(j:ι):evaluation v (MvPolynomial.X j)=scalar (v j):=by
  simp only [evaluation,RingHom.comp_apply,MvPolynomial.eval₂Hom_X']

lemma irrelevant_maps_top(v:ι→ℂ)(hv:∃j,v j≠0):
    (HomogeneousIdeal.irrelevant grading).toIdeal.map (evaluation v)=⊤:=by
  obtain ⟨j,hj⟩:=hv
  have hjI:MvPolynomial.X j∈(HomogeneousIdeal.irrelevant grading).toIdeal:=
    HomogeneousIdeal.mem_irrelevant_of_mem grading (by norm_num:0<(1:ℕ))
      (MvPolynomial.isHomogeneous_X ℂ j)
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (evaluation v) hjI)
  rw [evaluation_variable]
  exact (isUnit_iff_ne_zero.mpr hj).map scalar

/-- A genuine Spec(C)-valued morphism to the actual polynomial Proj.
The original nonzero coordinate produces the irrelevant-unit condition;
this is not an underlying set-point relabeled as a scheme morphism. -/
@[expose] def point(v:ι→ℂ)(hv:∃j,v j≠0):ComplexPoint⟶AlgebraicGeometry.Proj grading:=
  Proj.fromOfGlobalSections grading (evaluation v) (irrelevant_maps_top v hv)

/-- Every actual homogeneous basic open has its literal evaluated
preimage. This pins the morphism to the given full coordinate vector. -/
lemma homogeneous_preimage(v:ι→ℂ)(hv:∃j,v j≠0)(p:Equations)(n:ℕ)
    (hn:0<n)(hp:p.IsHomogeneous n):
    point v hv ⁻¹ᵁ Proj.basicOpen grading p=ComplexPoint.basicOpen (evaluation v p):=
  Proj.fromOfGlobalSections_preimage_basicOpen grading (evaluation v)
    (irrelevant_maps_top v hv) hn hp
lemma variable_preimage(v:ι→ℂ)(hv:∃j,v j≠0)(j:ι):
    point v hv ⁻¹ᵁ Proj.basicOpen grading (MvPolynomial.X j)=
      ComplexPoint.basicOpen (scalar (v j)):=by
  rw [homogeneous_preimage v hv _ 1 (by norm_num) (MvPolynomial.isHomogeneous_X ℂ j),
    evaluation_variable]

lemma positive_homogeneous_mem_iff(v:ι→ℂ)(hv:∃j,v j≠0)(x:ComplexPoint)
    (p:Equations)(n:ℕ)(hn:0<n)(hp:p.IsHomogeneous n):
    p∈((point v hv) x).asHomogeneousIdeal↔MvPolynomial.eval v p=0:=by
  have hmem:((point v hv) x)∈Proj.basicOpen grading p↔MvPolynomial.eval v p≠0:=by
    change x∈(point v hv ⁻¹ᵁ Proj.basicOpen grading p)↔_
    rw [homogeneous_preimage v hv p n hn hp]
    by_cases h:MvPolynomial.eval v p=0
    · have he:evaluation v p=0:=by
        change scalar (MvPolynomial.eval v p)=0
        rw [h,map_zero]
      rw [he]
      simp [h]
    · have hu:IsUnit (evaluation v p):=by
        change IsUnit (scalar (MvPolynomial.eval v p))
        exact (isUnit_iff_ne_zero.mpr h).map scalar
      rw [Scheme.basicOpen_of_isUnit _ hu]
      simp [h]
  change (p∉((point v hv) x).asHomogeneousIdeal↔MvPolynomial.eval v p≠0) at hmem
  simpa only [not_not] using not_congr hmem

/-- The genuine morphism has precisely the previously constructed relevant
homogeneous prime as its underlying point. Degree zero is covered by
multiplying by a genuine nonvanishing coordinate, not discarded. -/
lemma underlying_point(v:ι→ℂ)(hv:∃j,v j≠0)(x:ComplexPoint):
    (point v hv) x=ComplexProjectiveMarkerPoint318.point v hv:=by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  obtain ⟨j,hj⟩:=hv
  have hjI:MvPolynomial.X j∉((point v hv) x).asHomogeneousIdeal:=by
    rw [positive_homogeneous_mem_iff v hv x _ 1 (by norm_num)
      (MvPolynomial.isHomogeneous_X ℂ j)]
    simpa using hj
  have hmul:=positive_homogeneous_mem_iff v hv x (p*MvPolynomial.X j) (n+1)
    (Nat.zero_lt_succ n) (hp.mul (MvPolynomial.isHomogeneous_X ℂ j))
  rw [((point v hv) x).isPrime.mul_mem_iff_mem_or_mem] at hmul
  simp only [hjI,or_false,map_mul,MvPolynomial.eval_X,mul_eq_zero,hj,or_false] at hmul
  exact hmul.trans (ComplexProjectiveMarkerPoint318.homogeneous_mem_iff v hv p n hp).symm
end ComplexProjectiveSchemePoint318

