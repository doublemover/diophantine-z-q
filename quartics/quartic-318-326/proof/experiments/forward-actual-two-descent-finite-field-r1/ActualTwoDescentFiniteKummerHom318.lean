module
public import ActualTwoDescentFiniteRootKummerHom318
public section
noncomputable section
namespace ActualTwoDescentFiniteKummerHom318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]


open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteSimpleRootCoordinates318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentFiniteRootKummerHom318
variable [DecidableEq K]

lemma squareclass_square (q : SquareClass K) : q^2=1 := by
  refine QuotientGroup.induction_on q ?_
  intro u
  exact (QuotientGroup.eq_one_iff (u^2)).mpr ⟨u,rfl⟩

def kummerHom (n : K) (hn : n ≠ 0) : Multiplicative (Point n) →* (SquareClass K × SquareClass K) :=
  (rootKummerHom (firstRoot n hn)).prod (rootKummerHom (secondRoot n hn))

def kummerClass (n : K) (hn : n ≠ 0) (P : Point n) : SquareClass K × SquareClass K :=
  kummerHom n hn (Multiplicative.ofAdd P)

lemma kummer_class_zero (n : K) (hn : n ≠ 0) : kummerClass n hn 0=1 := (kummerHom n hn).map_one

lemma kummer_class_add (n : K) (hn : n ≠ 0) (P Q : Point n) :
    kummerClass n hn (P+Q)=kummerClass n hn P*kummerClass n hn Q :=
  (kummerHom n hn).map_mul _ _

lemma kummer_class_double (n : K) (hn : n ≠ 0) (P : Point n) : kummerClass n hn (P+P)=1 := by
  rw [kummer_class_add]
  apply Prod.ext
  · exact (pow_two (rootClass (firstRoot n hn) P)).symm.trans (squareclass_square _)
  · exact (pow_two (rootClass (secondRoot n hn) P)).symm.trans (squareclass_square _)

lemma root_class_one_iff {n : K} (R : SimpleRoot n) (P : Point n) :
    rootClass R P=1 ↔ ∃ s : K, s ≠ 0 ∧ rootCoordinate R P=s^2 := by
  rw [rootClass,←class_of_one,class_of_eq_iff]
  simp only [one_mul]

lemma kummer_one_roots (n : K) (hn : n ≠ 0) (P : Point n) (H : kummerClass n hn P=1) :
    (∃ s : K, s ≠ 0 ∧ rootCoordinate (firstRoot n hn) P=s^2) ∧
    (∃ t : K, t ≠ 0 ∧ rootCoordinate (secondRoot n hn) P=t^2) := by
  exact ⟨(root_class_one_iff _ _).mp (congrArg Prod.fst H),
    (root_class_one_iff _ _).mp (congrArg Prod.snd H)⟩

end ActualTwoDescentFiniteKummerHom318
