module
public import OriginalTernaryBoxCount318
public section
noncomputable section
namespace LiteralTernaryReduction318
open TernaryQuadraticLineCover318 TriangularLatticeBoxCount318
set_option maxHeartbeats 1000000

/-- LITERAL manuscript form after x=b-d,z=b+d: R=κw²-xz.
The preceding general engine used κw²-2xz; parameter doubling and exact
odd-modulus cancellation below are mandatory for its application here. -/
@[expose] def R (κ : ℤ) (v : Vector ℤ) : ℤ := κ*v.2.2^2-v.1*v.2.1

lemma prime_cancel_two (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (n : ℤ) :
    (p:ℤ)∣2*n ↔ (p:ℤ)∣n := by
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_mul,Int.cast_ofNat,mul_eq_zero,
    GoodReductionResidue318.two_residue_ne p hp2,false_or]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modulus_cancel_two (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (hp2 : ∀ i, p i≠2) (n : ℤ) :
    (FixedSquarefreeCRT318.modulus p:ℤ)∣2*n ↔ (FixedSquarefreeCRT318.modulus p:ℤ)∣n := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  rw [SquarefreeTernaryLatticeCover318.product_divisor_iff p hp hd,
    SquarefreeTernaryLatticeCover318.product_divisor_iff p hp hd]
  exact forall_congr' (fun i => prime_cancel_two (p i) (hp2 i) n)

lemma engine_identity (κ : ℤ) (v : Vector ℤ) :
    (2*κ)*v.2.2^2-2*v.1*v.2.1=2*R κ v := by dsimp [R]; ring

/-- Exact same integer coordinates and literal R; no unproved rescaling
or source identification is passed downstream. -/
theorem literal_cover (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (hp2 : ∀ i, p i≠2) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ) (v : Vector ℤ) :
    (FixedSquarefreeCRT318.modulus p:ℤ)∣R κ v ↔
      ∃ t : ∀ i, Option (ZMod (p i)),
        v∈SquarefreeTernaryLatticeCover318.lattice p hp (2*κ) t := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  have hk (i : ι) : ¬(p i:ℤ)∣2*κ := by
    intro h
    exact hκ i ((prime_cancel_two (p i) (hp2 i) κ).mp h)
  have hh := SquarefreeTernaryLatticeCover318.divisor_iff_lattice p hp hd (2*κ) hp2 hk v
  rwa [engine_identity,modulus_cancel_two p hp hd hp2] at hh

/-- The actual finite-slope code has coefficient κt², as required by
κw²-xz, not the engine's undoubled κt²/2. -/
theorem literal_finite_code (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (κ : ℤ) (t : ZMod p) (v : Vector ℤ) :
    TernaryCongruenceLattices318.integerCode p (2*κ) (some t) v=
      ((v.2.1:ZMod p)-(κ:ZMod p)*t^2*(v.1:ZMod p),(v.2.2:ZMod p)-t*(v.1:ZMod p)) := by
  apply Prod.ext
  · change (v.2.1:ZMod p)-((2*κ:ℤ):ZMod p)*t^2*(v.1:ZMod p)/2=_
    push_cast
    field_simp [GoodReductionResidue318.two_residue_ne p hp2]
    <;> ring
  · rfl

/-- Literal two-equation residue code, independently defined without division
by two. Both this code and the engine consume the very same integer vector. -/
@[expose] def literalIntegerCode (p : ℕ) (κ : ℤ) (t : Option (ZMod p)) :
    Vector ℤ →+ (ZMod p×ZMod p) where
  toFun v := match t with
    | none => ((v.1:ZMod p),(v.2.2:ZMod p))
    | some a => ((v.2.1:ZMod p)-(κ:ZMod p)*a^2*(v.1:ZMod p),
        (v.2.2:ZMod p)-a*(v.1:ZMod p))
  map_zero' := by cases t <;> simp
  map_add' v w := by cases t <;> simp [mul_add,sub_add_sub_comm]

theorem literal_integer_code_eq (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (κ : ℤ) (t : Option (ZMod p)) :
    literalIntegerCode p κ t=TernaryCongruenceLattices318.integerCode p (2*κ) t := by
  apply AddMonoidHom.ext
  intro v
  cases t with
  | none => rfl
  | some a => exact (literal_finite_code p hp2 κ a v).symm

@[expose] def literalGlobalCode (p : ι → ℕ) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) : Vector ℤ →+ (∀ i, ZMod (p i)×ZMod (p i)) :=
  AddMonoidHom.pi (fun i => literalIntegerCode (p i) κ (t i))

/-- An actual subgroup of Z³: the inverse image of zero under the literal
simultaneous residue code, not the image of a coordinate scaling map. -/
@[expose] def literalLattice (p : ι → ℕ) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) : AddSubgroup (Vector ℤ) :=
  (literalGlobalCode p κ t).ker

theorem literal_global_code_eq (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hp2 : ∀ i, p i≠2) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    literalGlobalCode p κ t=SquarefreeTernaryLatticeCover318.globalCode p hp (2*κ) t := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  apply AddMonoidHom.ext
  intro v
  funext i
  exact DFunLike.congr_fun (literal_integer_code_eq (p i) (hp2 i) κ (t i)) v

/-- Equality of integer subgroups, stronger than equality of their reductions
or their abstract cardinalities. The identity of Z³ realizes this equality. -/
theorem literal_lattice_eq (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hp2 : ∀ i, p i≠2) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    literalLattice p κ t=SquarefreeTernaryLatticeCover318.lattice p hp (2*κ) t := by
  unfold literalLattice SquarefreeTernaryLatticeCover318.lattice
  rw [literal_global_code_eq p hp hp2]

/-- The literal integer lattice index is q². There is no coordinate-map
index to multiply in: the preceding theorem is equality inside Z³ itself. -/
theorem literal_lattice_index (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) :
    (literalLattice p κ t).index=(FixedSquarefreeCRT318.modulus p)^2 := by
  rw [literal_lattice_eq p hp hp2]
  exact SquarefreeTernaryLatticeCover318.lattice_index p hp hd (2*κ) t

/-- The literal congruence cover in the independently defined integer lattices. -/
theorem literal_kernel_cover (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (hκ : ∀ i, ¬(p i:ℤ)∣κ) (v : Vector ℤ) :
    (FixedSquarefreeCRT318.modulus p:ℤ)∣R κ v ↔
      ∃ t : ∀ i, Option (ZMod (p i)), v∈literalLattice p κ t := by
  simp only [literal_lattice_eq p hp hp2]
  exact literal_cover p hp hd hp2 κ hκ v

@[expose] def LiteralBox (B : ℕ) (p : ι → ℕ) (κ : ℤ) :=
  {v : Box B // (FixedSquarefreeCRT318.modulus p:ℤ)∣R κ (coordinates v)}

/-- The literal original box and engine box at2κ are explicitly equivalent. -/
@[expose] def boxEquiv (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (hp2 : ∀ i, p i≠2) (κ : ℤ) :
    LiteralBox B p κ ≃ OriginalTernaryBoxCount318.DivisorBox B p (2*κ) where
  toFun v := ⟨v.1,by
    change (FixedSquarefreeCRT318.modulus p:ℤ)∣(2*κ)*(coordinates v.1).2.2^2-
      2*(coordinates v.1).1*(coordinates v.1).2.1
    rw [engine_identity,modulus_cancel_two p hp hd hp2]
    exact v.2⟩
  invFun v := ⟨v.1,by
    have hh := v.2
    change (FixedSquarefreeCRT318.modulus p:ℤ)∣(2*κ)*(coordinates v.1).2.2^2-
      2*(coordinates v.1).1*(coordinates v.1).2.1 at hh
    rwa [engine_identity,modulus_cancel_two p hp hd hp2] at hh⟩
  left_inv v := rfl
  right_inv v := rfl

/-- Actual literal-form count after the explicit source correction. -/
theorem literal_box_scaled (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ)
    (hB : FixedSquarefreeCRT318.modulus p≤B) :
    Nat.card (LiteralBox B p κ)*FixedSquarefreeCRT318.modulus p≤
      27*2^(Fintype.card ι)*B^3 := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  have hk (i : ι) : ¬(p i:ℤ)∣2*κ := by
    intro h
    exact hκ i ((prime_cancel_two (p i) (hp2 i) κ).mp h)
  rw [Nat.card_congr (boxEquiv B p hp hd hp2 κ)]
  exact OriginalTernaryBoxCount318.original_congruence_scaled B p hp hd (2*κ) hp2 hk hB

end LiteralTernaryReduction318
