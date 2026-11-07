module
public import DuplicationHeightArch318
public import DuplicationHeightLocal318
public import GlobalSquareHalving318
public section
namespace DuplicationProjective318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def F (a b:K) : K := (a^2+D*b^2)^2
@[expose] def G (a b:K) : K := 4*a*b*(a^2-D*b^2)
@[expose] def forms (Q:E.Point) : Fin 2→K := ![F (Q.xRep 0) (Q.xRep 1),G (Q.xRep 0) (Q.xRep 1)]

theorem ordinate_equation (x y:K) (h:E.Nonsingular x y) : y^2=x^3-D*x := by
  simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1

theorem nonzero_ordinate_scale (x y:K) (h:E.Nonsingular x y) (hy:y≠0) :
    F x 1=(4*y^2)*E.addX x x (E.slope x x y y) ∧ G x 1=4*y^2 := by
  constructor
  · rw [ValuationDuplication318.actual_doubling_x x y h hy]
    dsimp [F]
    field_simp [hy]
    ring
  · have he := ordinate_equation x y h
    dsimp [G]
    linear_combination -4*he

theorem zero_ordinate_scale (x:K) (h:E.Nonsingular x 0) : F x 1≠0 ∧ G x 1=0 := by
  have he := ordinate_equation x 0 h
  have hmul : x*(x^2-D)=0 := by linear_combination -he
  have hsum : x^2+D≠0 := by
    intro hz
    rcases mul_eq_zero.mp hmul with hx|hx
    · apply GlobalSquareHalving318.D_ne
      simpa [hx] using hz
    · have hd : D=0 := by linear_combination (hz-hx)/2
      exact GlobalSquareHalving318.D_ne hd
  constructor
  · simpa [F] using pow_ne_zero 2 hsum
  · dsimp [G]
    linear_combination 4*hmul

/-- The exact homogeneous duplication forms represent the actual doubled
point, including infinity and every 2-torsion branch. The scaling factor is
proved nonzero, so height invariance can be used without a totalized divide. -/
theorem forms_represent_double (Q:E.Point) :
    ∃s:K,s≠0 ∧ forms Q=s • ((2:ℤ) • Q).xRep := by
  cases Q with
  | zero =>
    refine ⟨1,one_ne_zero,?_⟩
    change forms (0:E.Point)=1 • ((2:ℤ) • (0:E.Point)).xRep
    rw [zsmul_zero]
    simp [forms,F,G,Point.xRep,zsmul_zero]
  | some x y h =>
    by_cases hy:y=0
    · subst y
      obtain ⟨hF,hG⟩ := zero_ordinate_scale x h
      refine ⟨F x 1,hF,?_⟩
      have hd : (2:ℤ) • Point.some x 0 h=0 := by
        rw [two_zsmul,Point.add_self_of_Y_eq]
        simp [negY,E]
      rw [hd]
      funext i
      fin_cases i <;> simp [forms,Point.xRep_some,Point.xRep_zero,hG]
    · obtain ⟨hF,hG⟩ := nonzero_ordinate_scale x y h hy
      refine ⟨4*y^2,mul_ne_zero (by norm_num) (pow_ne_zero 2 hy),?_⟩
      have hyn : y≠E.negY x y := by
        simp only [negY,E,zero_mul,sub_zero]
        intro he
        have hh : 2*y=0 := by linear_combination he
        exact (mul_ne_zero (by norm_num) hy) hh
      rw [two_zsmul,Point.add_self_of_Y_ne hyn]
      funext i
      fin_cases i <;> simp [forms,Point.xRep_some,hF,hG]

end
end DuplicationProjective318
