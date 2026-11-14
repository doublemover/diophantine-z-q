module
public import OriginalShortDualLattices318
public import Mathlib.Analysis.InnerProductSpace.PiL2
public section
noncomputable section
namespace OriginalEuclideanLattice318
open scoped BigOperators RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
set_option maxHeartbeats 2500000

abbrev E := EuclideanSpace ℝ (Fin 3)
@[expose] def embed (v : Vector ℤ) : E := WithLp.toLp 2 ![(v.1:ℝ),(v.2.1:ℝ),(v.2.2:ℝ)]

lemma embed_injective : Function.Injective embed := by
  intro v u he
  have hx : (v.1:ℝ)=(u.1:ℝ) := congrArg (fun x : E => x 0) he
  have hz : (v.2.1:ℝ)=(u.2.1:ℝ) := congrArg (fun x : E => x 1) he
  have hw : (v.2.2:ℝ)=(u.2.2:ℝ) := congrArg (fun x : E => x 2) he
  exact Prod.ext (by exact_mod_cast hx) (Prod.ext (by exact_mod_cast hz) (by exact_mod_cast hw))

lemma embed_zero : embed 0=0 := by ext i; fin_cases i <;> simp [embed]

lemma inner_embed (v u : Vector ℤ) : ⟪embed v,embed u⟫=(dot v u:ℝ) := by
  simp [embed,EuclideanSpace.inner_toLp_toLp,dotProduct,Fin.sum_univ_succ,dot,mul_comm]

lemma inner_embed_right (w : E) (u : Vector ℤ) :
    ⟪w,embed u⟫=w 0*(u.1:ℝ)+w 1*(u.2.1:ℝ)+w 2*(u.2.2:ℝ) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct,embed,dotProduct,Fin.sum_univ_succ,mul_comm]

@[expose] def embedHom : Vector ℤ →+ E where
  toFun := embed
  map_zero' := embed_zero
  map_add' v u := by ext i; fin_cases i <;> simp [embed]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal original integer subgroup embedded in STANDARD Euclidean
three-space, not an abstract isomorphic lattice with a changed metric. -/
@[expose] def realLattice (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    AddSubgroup E := (literalLattice p κ t).map embedHom

lemma mem_realLattice_iff (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (w : E) :
    w∈realLattice p κ t ↔ ∃ u : Vector ℤ, u∈literalLattice p κ t ∧ embed u=w := Iff.rfl

/-- The actual Euclidean integral dual: inner products with every point
of the embedded original integer lattice are integers. -/
@[expose] def Dual (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : AddSubgroup E where
  carrier := {w | ∀ u : E, u∈realLattice p κ t → ∃ n : ℤ, ⟪w,u⟫=(n:ℝ)}
  zero_mem' := by intro u hu; exact ⟨0,by simp⟩
  add_mem' := by
    intro w z hw hz u hu
    obtain ⟨a,ha⟩ := hw u hu
    obtain ⟨b,hb⟩ := hz u hu
    exact ⟨a+b,by simp only [inner_add_left,ha,hb,Int.cast_add]⟩
  neg_mem' := by
    intro w hw u hu
    obtain ⟨a,ha⟩ := hw u hu
    exact ⟨-a,by simp only [inner_neg_left,ha,Int.cast_neg]⟩

lemma dual_iff (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (w : E) :
    w∈Dual p κ t ↔ ∀ u : Vector ℤ, u∈literalLattice p κ t → ∃ n : ℤ, ⟪w,embed u⟫=(n:ℝ) := by
  constructor
  · intro hw u hu
    exact hw (embed u) ⟨u,hu,rfl⟩
  · intro hw u hu
    obtain ⟨v,hv,rfl⟩ := hu
    exact hw v hv

/-- Every original modulus multiple lies in the actual literal kernel.
This is independent of any prime-field inversion or coordinate scaling. -/
lemma modulus_multiple_mem (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (v : Vector ℤ) :
    ((FixedSquarefreeCRT318.modulus p:ℤ)*v.1,
      (FixedSquarefreeCRT318.modulus p:ℤ)*v.2.1,
      (FixedSquarefreeCRT318.modulus p:ℤ)*v.2.2)∈literalLattice p κ t := by
  change literalGlobalCode p κ t _=0
  funext i
  have hd : (p i:ℤ)∣(FixedSquarefreeCRT318.modulus p:ℤ) := by
    exact_mod_cast (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
  have hm : (FixedSquarefreeCRT318.modulus p:ZMod (p i))=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (FixedSquarefreeCRT318.modulus p:ℤ) (p i)).mpr hd
  change literalIntegerCode (p i) κ (t i) _=0
  cases t i <;> simp [literalIntegerCode,Int.cast_mul,hm]

end OriginalEuclideanLattice318
