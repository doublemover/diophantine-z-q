module
public import ThreeArithmeticQuotient318
public section
noncomputable section
namespace ThreeEffectiveSource318
open ThreeArithmeticPoint318 ThreeArithmeticQuotient318 OpenJComplexEvaluation318
open scoped MatrixGroups

lemma mod_three_unit_pairs (a d : ZMod 3) (h : a*d=1) :
    (a=1 ∧ d=1) ∨ (a= -1 ∧ d= -1) := by
  have hh : ∀a d : ZMod 3, a*d=1 → ((a=1 ∧ d=1) ∨ (a= -1 ∧ d= -1)) := by decide
  exact hh a d h

/-- At level three, every actual Gamma0 matrix is Gamma1 up to the
central sign. This is a special level-three statement, not a claim for general N. -/
theorem gamma0_eq_or_neg_gamma1 (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 3) :
    g ∈ CongruenceSubgroup.Gamma1 3 ∨ -g ∈ CongruenceSubgroup.Gamma1 3 := by
  have hc := CongruenceSubgroup.Gamma0_mem.mp hg
  have hd : (g 0 0:ZMod 3)*(g 1 1:ZMod 3)=1 := by
    have he := congrArg (Int.castRingHom (ZMod 3)) g.det_coe
    rw [Matrix.det_fin_two] at he
    simpa only [Int.coe_castRingHom,Int.cast_sub,Int.cast_mul,Int.cast_one,hc,mul_zero,sub_zero] using he
  rcases mod_three_unit_pairs _ _ hd with ⟨ha,hd⟩|⟨ha,hd⟩
  · exact Or.inl ((CongruenceSubgroup.Gamma1_mem 3 g).mpr ⟨ha,hd,hc⟩)
  · right
    apply (CongruenceSubgroup.Gamma1_mem 3 (-g)).mpr
    simpa only [Matrix.SpecialLinearGroup.coe_neg,Matrix.neg_apply,Int.cast_neg,ha,hd,hc,neg_neg,neg_zero]
      using (show (1:ZMod 3)=1 ∧ (1:ZMod 3)=1 ∧ (0:ZMod 3)=0 from ⟨rfl,rfl,rfl⟩)

/-- The genuine arithmetic point already respects the effective Gamma0(3)
action, because the extra central sign acts trivially on the upper half-plane. -/
theorem fixedPoint_gamma0_invariant (N : ℕ) [NeZero N] (g : SL(2,ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 3) (tau : UpperHalfPlane) (h : Admissible tau) :
    fixedPoint N (g•tau) (admissible_transform g tau h)=fixedPoint N tau h := by
  rcases gamma0_eq_or_neg_gamma1 g hg with hg|hg
  · exact fixedPoint_invariant N g hg tau h
  · simpa only [ModularGroup.SL_neg_smul] using fixedPoint_invariant N (-g) hg tau h

/-- The already-existing Gamma1(3) source quotient does not double count
the effective central sign: Gamma0(3) matrices give identical source points. -/
theorem quotient_gamma0_invariant (g : SL(2,ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 3) (tau : UpperHalfPlane) :
    GammaOneAtlas318.quotientMap 3 (g•tau)=GammaOneAtlas318.quotientMap 3 tau := by
  rcases gamma0_eq_or_neg_gamma1 g hg with hg|hg
  · exact (MarkedPeriod318.quotient_eq_iff_marked_transport 3 tau (g•tau)).mpr
      ⟨g,rfl,(MarkedPeriod318.point_stabilizer 3 g tau).mpr hg⟩
  · have he := (MarkedPeriod318.quotient_eq_iff_marked_transport 3 tau ((-g)•tau)).mpr
      ⟨-g,rfl,(MarkedPeriod318.point_stabilizer 3 (-g) tau).mpr hg⟩
    simpa only [ModularGroup.SL_neg_smul] using he

end ThreeEffectiveSource318
