module
public import FiniteStrictRadialExtension318
public import PELOriginalAllUnitMinimum318
public section
noncomputable section
namespace PELStrictPolygonExtension318
open PELDirichletOriginalUnits318 PELOriginalDirichletPolygon318

/-- The strict inequalities of the same original finite halfplane polygon. -/
@[expose] def strictInequalities (A B : ℝ) : Prop := ∀ (j : Fin 8) (ε δ : Bool),
  (rowFirst j:ℝ)*((sign ε:ℝ)*A)+(rowSecond j:ℝ)*((sign δ:ℝ)*B)<(rowConstant j:ℝ)

theorem weak_of_strict (A B : ℝ) (h : strictInequalities A B) : inequalities A B :=
  fun j ε δ => le_of_lt (h j ε δ)

/-- Every strict polygon point extends a positive distance radially while
staying in the SAME polygon. No unproved interior/convex-hull assertion. -/
theorem radial_extension (A B : ℝ) (h : strictInequalities A B) :
    ∃ t : ℝ, 1<t ∧ inequalities (t*A) (t*B) := by
  let I := Fin 8 × Bool × Bool
  let a : I → ℝ := fun i => (rowFirst i.1:ℝ)*((sign i.2.1:ℝ)*A)+
    (rowSecond i.1:ℝ)*((sign i.2.2:ℝ)*B)
  let c : I → ℝ := fun i => rowConstant i.1
  obtain ⟨δ,hδ,hall⟩ := FiniteStrictRadialExtension318.finite_slack
    (Finset.univ : Finset I) a c (fun i _ => h i.1 i.2.1 i.2.2)
  refine ⟨1+δ,by linarith,?_⟩
  intro j ε η
  have hi := hall (j,ε,η) (Finset.mem_univ _) δ (le_of_lt hδ) le_rfl
  dsimp [a,c] at hi
  convert le_of_lt hi using 1 <;> ring

/-- If an affine function is ≥1 on the whole polygon and equals1 at a
strict point, its value at the origin is also1. This is sufficient to force
an original norm-one unit into the exact central sign kernel. -/
theorem origin_equality (p q c A B : ℝ) (h : strictInequalities A B)
    (hmin : ∀ X Y : ℝ, inequalities X Y → 1≤p*X+q*Y+c)
    (heq : p*A+q*B+c=1) : c=1 := by
  obtain ⟨t,ht,hP⟩ := radial_extension A B h
  have hscale := hmin (t*A) (t*B) hP
  have hzero : inequalities 0 0 := by
    intro j ε δ
    fin_cases j <;> cases ε <;> cases δ <;>
      norm_num [rowFirst,rowSecond,rowConstant,sign]
  have hc := hmin 0 0 hzero
  have hid : p*(t*A)+q*(t*B)+c=t*(p*A+q*B+c)+(1-t)*c := by ring
  rw [hid,heq] at hscale
  norm_num at hc
  nlinarith
end PELStrictPolygonExtension318
