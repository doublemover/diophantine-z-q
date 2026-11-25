module

public import OriginalRetainedComplexPointsOverEEquiv318
public import OriginalCenteredAnalyticEquation318
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section
noncomputable section

namespace OriginalRetainedComplexAffineEquation318

open AlgebraicGeometry CategoryTheory

abbrev Polynomials (m : ℕ) := MvPolynomial (Fin 2 ⊕ Fin m) ℂ

variable {m : ℕ}

abbrev relationsIdeal (p : Fin m → Polynomials m) : Ideal (Polynomials m) :=
  Ideal.span (Set.range p)

abbrev coordinateQuotient (p : Fin m → Polynomials m) :=
  Polynomials m ⧸ relationsIdeal p

def scalar {B : Type} [CommRing B] (p : Fin m → Polynomials m)
    [Algebra (coordinateQuotient p) B] : ℂ →+* B :=
  (algebraMap (coordinateQuotient p) B).comp
    ((Ideal.Quotient.mk (relationsIdeal p)).comp (MvPolynomial.C : ℂ →+* Polynomials m))

def slot {B : Type} [CommRing B] (p : Fin m → Polynomials m)
    [Algebra (coordinateQuotient p) B] (i : Fin 2 ⊕ Fin m) : B :=
  algebraMap (coordinateQuotient p) B
    (Ideal.Quotient.mk (relationsIdeal p) (MvPolynomial.X i))

variable (p : Fin m → Polynomials m)

def eval (x : Fin 2 → ℂ) (y : Fin m → ℂ) : Polynomials m →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ) (Sum.elim x y)

theorem eval_kills {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i) = 0) : relationsIdeal p ≤ RingHom.ker (eval x y) := by
  apply Ideal.span_le.2
  rintro _ ⟨i, rfl⟩
  exact RingHom.mem_ker.2 (h i)

def evalQ {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i) = 0) : coordinateQuotient p →+* ℂ :=
  Ideal.Quotient.lift (relationsIdeal p) (eval x y)
    (fun _ hz => RingHom.mem_ker.1 (eval_kills p h hz))

variable {B : Type} [CommRing B] [Algebra (coordinateQuotient p) B]
variable (g : coordinateQuotient p) [loc : IsLocalization.Away g B]

def evalAt {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i) = 0) (hg : evalQ p h g ≠ 0) : B →+* ℂ :=
  IsLocalization.Away.lift (S := B) (g := evalQ p h) g (isUnit_iff_ne_zero.2 hg)

theorem scalar_read {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i) = 0) (hg : evalQ p h g ≠ 0) :
    (evalAt p g h hg : B →+* ℂ).comp (scalar p : ℂ →+* B) = RingHom.id ℂ := by
  apply RingHom.ext
  intro t
  change IsLocalization.Away.lift (S := B) (g := evalQ p h) g (isUnit_iff_ne_zero.2 hg)
    (algebraMap (coordinateQuotient p) B (Ideal.Quotient.mk (relationsIdeal p) (MvPolynomial.C t))) = t
  rw [IsLocalization.Away.lift_eq, evalQ, Ideal.Quotient.lift_mk, eval,
    MvPolynomial.eval₂Hom_C, RingHom.id_apply]

theorem slot_read {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i) = 0) (hg : evalQ p h g ≠ 0) (i : Fin 2 ⊕ Fin m) :
    (evalAt p g h hg : B →+* ℂ) (slot p i) = Sum.elim x y i := by
  change IsLocalization.Away.lift (S := B) (g := evalQ p h) g (isUnit_iff_ne_zero.2 hg)
    (algebraMap (coordinateQuotient p) B (Ideal.Quotient.mk (relationsIdeal p) (MvPolynomial.X i))) = _
  rw [IsLocalization.Away.lift_eq, evalQ, Ideal.Quotient.lift_mk, eval,
    MvPolynomial.eval₂Hom_X']

include loc in
/-- Actual whole affine ring maps, not just a point of the normalization,
are determined by the original scalar and original evaluations. -/
theorem maps_unique (u v : B →+* ℂ)
    (hc : u.comp (scalar p) = v.comp (scalar p))
    (hi : ∀ i, u (slot p i) = v (slot p i)) : u=v := by
  apply IsLocalization.ringHom_ext (R := coordinateQuotient p) (S := B) (Submonoid.powers g)
  apply Ideal.Quotient.ringHom_ext (I := relationsIdeal p)
  exact MvPolynomial.ringHom_ext' hc hi

variable {A Y E : Scheme} (a : A⟶Y) (P33 : E⟶Y)
  (σ : Spec (.of ℂ) ⟶ E)

local notation "Aσ" => OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33)

/-- The inverse chart point is given by Spec of the evaluation in the
actual selected origin-open ring B; compose with the already fixed open
of the literal F33. The old F33/C and E-relative point are then equivalent
by the old actual R121 constructor. -/
def markedPoint (j : Spec (.of B)⟶(Aσ).left)
    (hj : j≫(Aσ).hom = Spec.map (CommRingCat.ofHom (scalar p : ℂ →+* B)))
    {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i) = 0) (hg : evalQ p h g ≠ 0) :
    Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Aσ := by
  let e : B →+* ℂ := evalAt p g h hg
  refine Over.homMk (Spec.map (CommRingCat.ofHom e)≫j) ?_
  rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hr : e.comp (scalar p) = RingHom.id ℂ := scalar_read p g h hg
  rw [hr, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem markedPoint_is_literal (j : Spec (.of B)⟶(Aσ).left)
    (hj : j≫(Aσ).hom = Spec.map (CommRingCat.ofHom (scalar p : ℂ →+* B)))
    {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i) = 0) (hg : evalQ p h g ≠ 0) :
    (markedPoint p g a P33 σ j hj h hg).left =
      Spec.map (CommRingCat.ofHom (evalAt p g h hg : B →+* ℂ))≫j := rfl

section InverseChart

/-- The analytic residual is defined by the actual polynomial tuple and
the actual invertible matrix J; it is not an analytic map independent of
the selected chart. In translated coordinates retaining its first two
variables, use J = ∂P/∂y(0,0). -/
def residual (J : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ))
    (x : Fin 2 → ℂ) (y : Fin m → ℂ) : Fin m → ℂ :=
  y - J.symm (fun i => eval x y (p i))

theorem residual_zero (J : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ))
    (x : Fin 2 → ℂ) (y : Fin m → ℂ)
    (h : y-residual p J x y=0) : ∀ i, eval x y (p i)=0 := by
  unfold residual at h
  rw [sub_sub_cancel] at h
  have hv := congrArg J h
  rw [LinearEquiv.apply_symm_apply, map_zero] at hv
  intro i
  exact congrFun hv i

/-- Construct a genuine family of points of the one original selected
complex fibre, from a centered presentation of its genuine open. The
two free coordinates are its original generators; the implicit branch
is proved, rather than supplied in the inputs. -/
theorem exists_marked_inverse_chart
    (j : Spec (.of B)⟶(Aσ).left)
    (hj : j≫(Aσ).hom = Spec.map (CommRingCat.ofHom (scalar p : ℂ →+* B)))
    (J : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ))
    (G : Polynomials m) (hG : Ideal.Quotient.mk (relationsIdeal p) G = g) {r ρ q : ℝ}
    (hρ : 0 < ρ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h0 : ∀ x, ‖x‖ ≤ r → ‖residual p J x 0‖ ≤ (1-q)*ρ)
    (hLip : ∀ x, ‖x‖ ≤ r → ∀ y y', ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ →
      ‖residual p J x y-residual p J x y'‖ ≤ q*‖y-y'‖)
    (hD : ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ ρ → eval x y G ≠ 0) :
    let D := {x : Fin 2 → ℂ // ‖x‖ ≤ r}
    ∃ y : D → (Fin m → ℂ),
    ∃ h : ∀ x : D, ∀ i, eval x.val (y x) (p i)=0,
    ∃ unit : ∀ x : D, evalQ p (h x) g≠0,
    ∃ pts : D → (Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Aσ),
      (∀ x : D, ‖y x‖ ≤ ρ) ∧
      (∀ x : D, pts x = markedPoint p g a P33 σ j hj (h x) (unit x)) ∧
      (∀ x : D, ∀ i : Fin 2,
        (evalAt p g (h x) (unit x) : B →+* ℂ) (slot p (.inl i)) = x.val i) := by
  let D := {x : Fin 2 → ℂ // ‖x‖ ≤ r}
  obtain ⟨y, hy, _⟩ := OriginalCenteredAnalyticEquation318.zeroChart
    (residual p J) hρ hq0 hq1 h0 hLip
  have h : ∀ x : D, ∀ i, eval x.val (y x.val) (p i)=0 :=
    fun x => residual_zero p J x.val (y x.val) (hy x.val x.property).2
  have hu : ∀ x : D, evalQ p (h x) g≠0 := by
    intro x
    rw [← hG, evalQ, Ideal.Quotient.lift_mk]
    exact hD x.val (y x.val) x.property (hy x.val x.property).1
  refine ⟨fun x => y x.val, h, hu,
    fun x => markedPoint p g a P33 σ j hj (h x) (hu x), ?_, ?_, ?_⟩
  · intro x
    exact (hy x.val x.property).1
  · intro x
    rfl
  · intro x i
    exact slot_read p g (h x) (hu x) (.inl i)

end InverseChart

end OriginalRetainedComplexAffineEquation318
