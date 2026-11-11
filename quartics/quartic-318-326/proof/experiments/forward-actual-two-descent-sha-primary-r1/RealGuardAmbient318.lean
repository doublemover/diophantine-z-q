module
public import RealQuarticAmbient318
public section
noncomputable section
namespace RealGuardAmbient318
open Set RealQuarticAmbient318
open LocalGenerator318 (P)
set_option maxHeartbeats 1000000

/-- The literal rational-coefficient guard as a polynomial on the actual
finite real-coordinate ambient space. No new topology is imposed. -/
@[expose] def guard (j : Fin 4) (z : Ambient) : ℝ :=
  ((z (j.natAdd 4,0,0)^2-z (j.castAdd 4,0,0)^2)+
   (z (j.natAdd 4,1,0)^2-z (j.castAdd 4,1,0)^2))/2

theorem guard_analytic (j : Fin 4) : AnalyticOnNhd ℝ (guard j) univ := by
  intro z _
  exact (((coordinate_analytic _ z).pow 2).sub ((coordinate_analytic _ z).pow 2)).add
    (((coordinate_analytic _ z).pow 2).sub ((coordinate_analytic _ z).pow 2)) |>.div
      analyticAt_const (by norm_num)

theorem guard_continuous (j : Fin 4) : Continuous (guard j) :=
  continuousOn_univ.mp (guard_analytic j).continuousOn

/-- Uniform bounds on the actual compact real source model. Inverse-guard
bounds still require a separate nonzero compact region. -/
theorem guard_bound (j : Fin 4) {z : Ambient} (hz : z∈ovals) : |guard j z|≤1 := by
  have hb (i : Fin 8) (e : Fin 2) : z (i,e,0)^2≤1 :=
    (sq_le_one_iff_abs_le_one _).mpr (coordinate_bound hz i e 0)
  have h0 := hb (j.castAdd 4) 0
  have h1 := hb (j.castAdd 4) 1
  have h2 := hb (j.natAdd 4) 0
  have h3 := hb (j.natAdd 4) 1
  have h4 := sq_nonneg (z (j.castAdd 4,0,0))
  have h5 := sq_nonneg (z (j.castAdd 4,1,0))
  have h6 := sq_nonneg (z (j.natAdd 4,0,0))
  have h7 := sq_nonneg (z (j.natAdd 4,1,0))
  unfold guard
  apply abs_le.mpr
  constructor <;> linarith

/-- Exact comparison for every integer h, including zero and all negative
indices. It is the original rational trace guard, not just its sign. -/
theorem guard_orbit (n : Fin 4 → ℤ) (h : ℤ) (j : Fin 4) :
    guard j (orbit n h)=(RealGuardTrace318.guardValue (n j) (h • P) : ℝ) := by
  rw [←RealGuardTrace318.literal_guard (CoherentMultiplePrefix318.u n h)
    (CoherentMultiplePrefix318.v n h) j (n j) (h • P)
    (CoherentMultiplePrefix318.curves n h) (CoherentMultiplePrefix318.left_point n h j)
    (CoherentMultiplePrefix318.right_point n h j),RealGuardTrace318.real_coefficient]
  simp only [guard,orbit,embedding,RealGuardWitness318.denominator,
    ite_true,ite_false,show (1:Fin 2)≠0 by decide,map_sub,map_pow]

/-- The same identity point in the actual orbit closure makes all nonzero
label guards strictly positive. No nontriviality hypothesis is added. -/
theorem identity_guard_positive (n : Fin 4 → ℤ) (j : Fin 4) (hn : n j≠0) :
    0<guard j (orbit n 0) := by
  rw [guard_orbit,zero_zsmul]
  exact_mod_cast RealGuardTrace318.guard_at_identity_positive (n j) hn

/-- There is a genuine open ambient neighborhood of the same identity orbit
point on which all four literal real guards are simultaneously positive. -/
theorem simultaneous_identity_neighborhood (n : Fin 4 → ℤ) (hn : ∀ j, n j≠0) :
    ∃ U : Set Ambient, IsOpen U ∧ orbit n 0∈U ∧
      ∀ z∈U, ∀ j : Fin 4, 0<guard j z := by
  refine ⟨⋂ j, {z | 0<guard j z},?_,?_,?_⟩
  · exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (guard_continuous j)
  · exact mem_iInter.mpr fun j => identity_guard_positive n j (hn j)
  · intro z hz j
    exact mem_iInter.mp hz j

/-- This restriction is continuous on the compact actual orbit closure. -/
theorem guard_on_closure_continuous (n : Fin 4 → ℤ) (j : Fin 4) :
    Continuous (fun z : orbitClosure n => guard j z.val) :=
  (guard_continuous j).comp continuous_subtype_val

/-- A global analytic identity on the ambient space is ruled out. This does
not assert density of the nonzero locus on an arbitrary orbit component. -/
theorem guard_not_identically_zero (n : Fin 4 → ℤ) (j : Fin 4) (hn : n j≠0) :
    ¬(∀ z : Ambient, guard j z=0) := by
  intro he
  exact (ne_of_gt (identity_guard_positive n j hn)) (he (orbit n 0))

end RealGuardAmbient318
