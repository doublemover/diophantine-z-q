module
public import FourTorsionQuotient318
public section
noncomputable section
namespace ActualFourTorsion318
open GoodReductionResidue318 GoodReductionLifting318 GoodReductionCardinality318
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

lemma square_unit (a : ℤ_[p]) (ha : ‖a‖=1) : ‖a^2‖=1 := by rw [norm_pow,ha,one_pow]
@[expose] def zeroRoot (a : ℤ_[p]) : IntegralCurve p (a^2) := ⟨(0,0),by ring⟩
@[expose] def positiveRoot (a : ℤ_[p]) : IntegralCurve p (a^2) := ⟨(a,0),by ring⟩

lemma ordinate_zero_double (D : ℤ_[p]) (hD : ‖D‖=1) (P : IntegralCurve p D)
    (hy : P.1.2=0) : point p D hD P+point p D hD P=0 := by
  unfold point
  apply Point.add_self_of_Y_eq
  simp only [hy,PadicInt.coe_zero,negY,E,zero_mul,sub_zero,neg_zero]

lemma class_nonzero (D : ℤ_[p]) (hD : ‖D‖=1) (P : IntegralCurve p D) :
    QuotientAddGroup.mk' (subgroup p D) (point p D hD P)≠0 := by
  intro he
  exact point_nonformal p D hD P ((QuotientAddGroup.eq_zero_iff (subgroup p D)).mp he)

/-- The actual0 and+a affine2-torsion points have distinct nonzero classes
in the SAME formal quotient. Unit a excludes all residue collisions. -/
theorem distinct_torsion (a : ℤ_[p]) (ha : ‖a‖=1) :
    let q := QuotientAddGroup.mk' (subgroup p (a^2))
    let A := q (point p (a^2) (square_unit p a ha) (zeroRoot p a))
    let B := q (point p (a^2) (square_unit p a ha) (positiveRoot p a))
    A+A=0 ∧ B+B=0 ∧ A≠0 ∧ B≠0 ∧ A≠B := by
  dsimp only
  refine ⟨?_,?_,class_nonzero p _ _ _,class_nonzero p _ _ _,?_⟩
  · rw [←map_add,ordinate_zero_double p _ _ _ rfl,map_zero]
  · rw [←map_add,ordinate_zero_double p _ _ _ rfl,map_zero]
  · intro he
    have hr := same_coset_residue p (a^2) (square_unit p a ha) (zeroRoot p a) (positiveRoot p a) he
    have hx := congrArg (fun z : ResidueCurve p (a^2) => z.1.1) hr
    have hh : PadicInt.toZMod a=0 := by simpa only [reduce,zeroRoot,positiveRoot,map_zero] using hx.symm
    exact ((residue_unit p a).mpr ha) hh

/-- The stronger quarter-cardinality bound now holds for every actual
double in the original good-reduction quotient. Its hypotheses include a
literal square unit coefficient and the explicit four torsion classes. -/
theorem doubled_order_dvd_quarter (hp : p≠2) (a : ℤ_[p]) (ha : ‖a‖=1)
    (Q : (E ((a^2:ℤ_[p]):ℚ_[p])).Point) :
    addOrderOf (QuotientAddGroup.mk' (subgroup p (a^2)) (Q+Q))∣
      (1+Nat.card (ResidueCurve p (a^2)))/4 := by
  let q := QuotientAddGroup.mk' (subgroup p (a^2))
  letI : Finite ((E ((a^2:ℤ_[p]):ℚ_[p])).Point ⧸ subgroup p (a^2)) :=
    Finite.of_equiv (Option (ResidueCurve p (a^2))) (equivalence p hp (a^2) (square_unit p a ha))
  obtain ⟨hAA,hBB,hA,hB,hAB⟩ := distinct_torsion p a ha
  have he := FourTorsionQuotient318.double_order_dvd_quarter _ _ hAA hBB hA hB hAB (q Q)
  rw [←map_add,cardinality p hp (a^2) (square_unit p a ha)] at he
  exact he

theorem doubled_order_dvd_quarter_of_square (hp : p≠2) (D a : ℤ_[p])
    (ha : ‖a‖=1) (hD : D=a^2) (Q : (E (D:ℚ_[p])).Point) :
    addOrderOf (QuotientAddGroup.mk' (subgroup p D) (Q+Q))∣
      (1+Nat.card (ResidueCurve p D))/4 := by
  subst D
  exact doubled_order_dvd_quarter p hp a ha Q

end ActualFourTorsion318
