module
public import OriginalShearedOffsetNonzero318
public section
noncomputable section
namespace OriginalOffsetZeroLocus318
open scoped BigOperators
open MvPolynomial TernaryQuadraticLineCover318 IntegerResidueBoxCount318
open OriginalOffsetEliminant318 OriginalShearedOffsetNonzero318
open OriginalAffineSieveEliminants318 OriginalBoundedIntegerShear318
open OriginalControlledIntegralBasis318
set_option maxHeartbeats 7500000

@[expose] def GridZeros (f : MvPolynomial (Fin 2) ℤ) (S T : Finset ℤ) :=
  {a : ↥S×↥T // eval ![a.1.1,a.2.1] f=0}

/-- Anisotropic integer grid count from the pinned exact Schwartz-Zippel
statement. Different side lengths remain separate throughout. -/
theorem grid_zero_count (f : MvPolynomial (Fin 2) ℤ) (hf : f≠0)
    (D : ℕ) (hD : f.totalDegree≤D) (S T : Finset ℤ) (hS : 0<S.card) (hT : 0<T.card) :
    Nat.card (GridZeros f S T)≤D*(S.card+T.card) := by
  classical
  let sets : Fin 2 → Finset ℤ := ![S,T]
  let Z := (Fintype.piFinset sets).filter (fun a => eval a f=0)
  let map : GridZeros f S T → ↥Z := fun a => ⟨![a.1.1.1,a.1.2.1],by
    apply Finset.mem_filter.mpr
    refine ⟨?_,a.2⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · exact a.1.1.2
    · exact a.1.2.2⟩
  have hi : Function.Injective map := by
    intro a b he
    have hh := congrArg Subtype.val he
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrFun hh 0)
    · exact Subtype.ext (congrFun hh 1)
  have hc : Nat.card (GridZeros f S T)≤Z.card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective map hi
  have hs := schwartz_zippel_sum_degreeOf hf sets
  have hs' : (Z.card:ℚ≥0)/((S.card:ℚ≥0)*T.card)≤
      (f.degreeOf 0:ℚ≥0)/S.card+(f.degreeOf 1:ℚ≥0)/T.card := by
    simpa [Z,sets,Fin.prod_univ_two,Fin.sum_univ_two] using hs
  have hspos : (0:ℚ≥0)<S.card := by exact_mod_cast hS
  have htpos : (0:ℚ≥0)<T.card := by exact_mod_cast hT
  have hh := (div_le_iff₀ (mul_pos hspos htpos)).mp hs'
  have he : ((f.degreeOf 0:ℚ≥0)/S.card+(f.degreeOf 1:ℚ≥0)/T.card)*
      ((S.card:ℚ≥0)*T.card)=(f.degreeOf 0:ℚ≥0)*T.card+(f.degreeOf 1:ℚ≥0)*S.card := by
    field_simp [ne_of_gt hspos,ne_of_gt htpos]
    <;> ring
  rw [he] at hh
  have hd0 : f.degreeOf 0≤D := (degreeOf_le_totalDegree f 0).trans hD
  have hd1 : f.degreeOf 1≤D := (degreeOf_le_totalDegree f 1).trans hD
  have hnat : Z.card≤f.degreeOf 0*T.card+f.degreeOf 1*S.card := by exact_mod_cast hh
  calc
    _ ≤ Z.card := hc
    _ ≤ f.degreeOf 0*T.card+f.degreeOf 1*S.card := hnat
    _ ≤ D*T.card+D*S.card := Nat.add_le_add (Nat.mul_le_mul_right _ hd0) (Nat.mul_le_mul_right _ hd1)
    _ = D*(S.card+T.card) := by ring

lemma interval_card (A : ℕ) : (Finset.Icc (-(A:ℤ)) (A:ℤ)).card=2*A+1 := by
  rw [Int.card_Icc]
  omega

@[expose] def ZeroOffsets (side coordinate : Bool) (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ) :=
  {a : Interval A×Interval B // normEliminant side κ t (offset u v a.1.1 a.2.1) d coordinate=0}

lemma actual_zero_offsets (side coordinate : Bool) (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ)
    (hn : polynomial side coordinate κ t u v d≠0) :
    Nat.card (ZeroOffsets side coordinate κ t u v d A B)≤4*((2*A+1)+(2*B+1)) := by
  have hh := grid_zero_count (polynomial side coordinate κ t u v d) hn 4
    (degree side coordinate κ t u v d) (Finset.Icc (-(A:ℤ)) A) (Finset.Icc (-(B:ℤ)) B)
    (by rw [interval_card]; omega) (by rw [interval_card]; omega)
  simpa only [GridZeros,ZeroOffsets,Interval,actual_eval,interval_card] using hh

@[expose] def EitherZero (side : Bool) (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ) :=
  {a : Interval A×Interval B // ∃ coordinate : Bool,
    normEliminant side κ t (offset u v a.1.1 a.2.1) d coordinate=0}

/-- The actual two exceptional offset loci are counted by UNION, not
assumed disjoint or discarded. Each nonzero polynomial has degree<=4. -/
theorem either_zero_offsets (side : Bool) (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ)
    (hn : ∀ coordinate, polynomial side coordinate κ t u v d≠0) :
    Nat.card (EitherZero side κ t u v d A B)≤8*((2*A+1)+(2*B+1)) := by
  classical
  have hc := OriginalFiniteSieveUnion318.finite_union_card
    (fun coordinate : Bool => fun a : Interval A×Interval B =>
      normEliminant side κ t (offset u v a.1.1 a.2.1) d coordinate=0)
  have h0 := actual_zero_offsets side false κ t u v d A B (hn false)
  have h1 := actual_zero_offsets side true κ t u v d A B (hn true)
  simp only [Fintype.sum_bool] at hc
  change Nat.card (EitherZero side κ t u v d A B)≤_ at hc
  change Nat.card (ZeroOffsets side true κ t u v d A B)+
    Nat.card (ZeroOffsets side false κ t u v d A B)≥_ at hc
  omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Full actual zero-offset CYLINDER in the same bounded shear. Every
short-coordinate value is retained, so no bad fiber is silently removed. -/
theorem original_zero_cylinder (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (κ t : ℤ)
    (hκ : κ≠0) (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z) (i j : ℤ)
    (hw : (shear i j u v z).2.2≠0) (side : Bool) (ht : side=true → t+2≠0)
    (A B C : ℕ) :
    Nat.card (EitherZero side κ t u v (shear i j u v z) A B × Interval C)≤
      8*((2*A+1)+(2*B+1))*(2*C+1) := by
  have hc := either_zero_offsets side κ t u v (shear i j u v z) A B
    (fun coordinate => actual_offset_nonzero q hq κ t hκ s u v z hb i j hw side coordinate ht)
  have hI : Nat.card (Interval C)=2*C+1 := by
    simpa only [Nat.card_eq_fintype_card,Interval,Fintype.card_coe] using interval_card C
  rw [Nat.card_prod,hI]
  exact Nat.mul_le_mul_right _ hc

end OriginalOffsetZeroLocus318
