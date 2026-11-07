module
public import GlobalReductionCounts318
public section
namespace GlobalNormClasses318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The actual rational norm-square predicate on the x-coordinate, with
identity xRep 0=1 and the x=0 two-torsion point both included. -/
@[expose] def NormSquare (Q:E.Point) : Prop := IsSquare (AnchorNorm318.norm (Q.xRep 0))

/-- Exhaustion of the actual 2-torsion subgroup requires no global descent. -/
theorem two_torsion_classification (Q:E.Point) (hQ:Q+Q=0) : Q=0 ∨ ∃i:Fin 3,Q=T i := by
  cases Q with
  | zero => exact Or.inl rfl
  | some x y h =>
    have hyn : y=E.negY x y := by
      by_contra hn
      rw [Point.add_self_of_Y_ne hn] at hQ
      exact Point.some_ne_zero _ hQ
    have hy : y=0 := by
      simp only [negY,E,zero_mul,sub_zero] at hyn
      have hh : 2*y=0 := by linear_combination hyn
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
    subst y
    have he := h.1
    rw [equation_iff] at he
    have hf : x*(x^2-D)=0 := by
      simp only [E,zero_mul,mul_zero,add_zero,zero_pow (by decide : 2≠0)] at he
      linear_combination -he
    right
    rcases mul_eq_zero.mp hf with hx|hx
    · subst x
      exact ⟨0,rfl⟩
    · have hs : x^2=(3-i)^2 := by simpa only [D] using sub_eq_zero.mp hx
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with hp|hm
      · have hh : x=pair 3 (-1) := by rw [hp]; ext <;> norm_num [i,pair]
        refine ⟨1,?_⟩
        rw [T,Point.some.injEq]
        exact ⟨hh,rfl⟩
      · have hh : x=pair (-3) 1 := by rw [hm]; ext <;> norm_num [i,pair]
        refine ⟨2,?_⟩
        rw [T,Point.some.injEq]
        exact ⟨hh,rfl⟩

theorem torsion_norm_square (i:Fin 3) : NormSquare (T i) ↔ i=0 := by
  fin_cases i
  · simp [NormSquare,T,torsionX,Point.xRep_some,AnchorNorm318.norm]
  · have hn : ¬IsSquare (7:ℚ) := by decide +kernel
    norm_num [NormSquare,T,torsionX,Point.xRep_some,AnchorNorm318.norm_pair]
  · have hn : ¬IsSquare (7:ℚ) := by decide +kernel
    norm_num [NormSquare,T,torsionX,Point.xRep_some,AnchorNorm318.norm_pair]

theorem R_not_norm_square : ¬NormSquare R := by
  intro h
  have hn := h.nonneg
  norm_num [NormSquare,R,xR,Point.xRep_some,AnchorNorm318.norm_pair] at hn

theorem translate_not_norm_square (i:Fin 3) : ¬NormSquare (R+T i) := by
  intro h
  obtain ⟨y,hn,he⟩ := translate_coordinates i
  rw [he] at h
  have hh := h.nonneg
  fin_cases i <;>
    norm_num [NormSquare,translateX,Point.xRep_some,AnchorNorm318.norm_pair] at hh

/-- Among actual 2-torsion points, norm-square membership selects precisely
O and the x=0 point. This is the torsion part of the required H coset theorem. -/
theorem norm_square_two_torsion (Q:E.Point) (hQ:Q+Q=0) (hn:NormSquare Q) :
    Q=0 ∨ Q=T 0 := by
  rcases two_torsion_classification Q hQ with h0|⟨i,hi⟩
  · exact Or.inl h0
  · right
    rw [hi] at hn
    have hz := (torsion_norm_square i).mp hn
    simpa [hz] using hi

end
end GlobalNormClasses318
