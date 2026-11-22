module
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Order.Filter.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

open Filter

namespace PointwiseConverseOuterDefect

universe u v
variable {ι : Type u}

/-- Reduction in the actual integral target (after reconstructing and
then passing to the localized/completed model). -/
def twoAdicReduction (R : Type v) [CommRing R] (n : ℕ) :
    R →+* (R ⧸ Ideal.span {(2 : R) ^ n}) :=
  Ideal.Quotient.mk _

theorem twoAdicReduction_eq_zero_iff (R : Type v) [CommRing R] (n : ℕ) (a : R) :
    twoAdicReduction R n a = 0 ↔ (2 : R) ^ n ∣ a :=
  Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

/-- The divisibility formulation of the outer valuation ideal.
For the actual target each R j is a DVR with uniformizer 2. -/
def Vanishes (F : Filter ι) (R : ι → Type v) [∀ j, CommRing (R j)]
    (x : ∀ j, R j) : Prop :=
  ∀ n : ℕ, ∀ᶠ j in F, (2 : R j) ^ n ∣ x j

theorem vanishes_iff_reduces_to_zero (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] (x : ∀ j, R j) :
    Vanishes F R x ↔ ∀ n : ℕ, ∀ᶠ j in F, twoAdicReduction (R j) n (x j) = 0 := by
  constructor
  · intro h n
    exact (h n).mono (fun j hj => (twoAdicReduction_eq_zero_iff (R j) n (x j)).mpr hj)
  · intro h n
    exact (h n).mono (fun j hj => (twoAdicReduction_eq_zero_iff (R j) n (x j)).mp hj)

def valuationIdeal (F : Filter ι) (R : ι → Type v) [∀ j, CommRing (R j)] :
    Ideal (∀ j, R j) where
  carrier := {x | Vanishes F R x}
  zero_mem' := fun _ => Filter.Eventually.of_forall (fun _ => dvd_zero _)
  add_mem' := by
    intro x y hx hy n
    exact ((hx n).and (hy n)).mono (fun _ h => dvd_add h.1 h.2)
  smul_mem' := by
    intro f x hx n
    refine (hx n).mono ?_
    intro j hj
    obtain ⟨z, hz⟩ := hj
    refine ⟨f j * z, ?_⟩
    change f j * x j = (2 : R j) ^ n * (f j * z)
    rw [hz, ← mul_assoc, mul_comm (f j) ((2 : R j) ^ n), mul_assoc]

/-- This is a ring morphism on integral families, not division by a
clearing factor and not specialization from a truncated t-quotient. -/
def outerReduction (F : Filter ι) (R : ι → Type v) [∀ j, CommRing (R j)] :
    (∀ j, R j) →+* ((∀ j, R j) ⧸ valuationIdeal F R) :=
  Ideal.Quotient.mk (valuationIdeal F R)

theorem outerReduction_eq_zero_iff (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] (x : ∀ j, R j) :
    outerReduction F R x = 0 ↔ Vanishes F R x :=
  Ideal.Quotient.eq_zero_iff_mem

theorem outerReduction_eq_of_eventually (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] (x y : ∀ j, R j) (h : ∀ᶠ j in F, x j = y j) :
    outerReduction F R x = outerReduction F R y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (outerReduction_eq_zero_iff F R (x - y)).mpr
  intro n
  refine h.mono ?_
  intro j hj
  change (2 : R j) ^ n ∣ x j - y j
  rw [hj, sub_self]
  exact dvd_zero _

/-- Vector version, expressed with a common integral divisibility witness
on the eventual set for each exponent. -/
def VectorVanishes (F : Filter ι) (R : ι → Type v) [∀ j, CommRing (R j)]
    (d : ℕ) (x : ∀ j, Fin d → R j) : Prop :=
  ∀ n : ℕ, ∀ᶠ j in F, ∃ z : Fin d → R j, x j = ((2 : R j) ^ n) • z

theorem vectorVanishes_of_coordinates (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] (d : ℕ) (x : ∀ j, Fin d → R j)
    (h : ∀ k : Fin d, Vanishes F R (fun j => x j k)) :
    VectorVanishes F R d x := by
  intro n
  have hn : ∀ᶠ j in F, ∀ k : Fin d, (2 : R j) ^ n ∣ x j k :=
    Filter.eventually_all.mpr (fun k => h k n)
  refine hn.mono ?_
  intro j hj
  refine ⟨fun k => Classical.choose (hj k), ?_⟩
  funext k
  exact Classical.choose_spec (hj k)

/-- An actual integral coordinate map with one fixed clearing exponent
cannot prevent an outer-small defect from vanishing. The output is already
assumed integral, and the cleared vector identity is supplied, not inferred. -/
theorem cleared_defect_zero (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] [∀ j, IsDomain (R j)]
    (two_ne_zero : ∀ j, (2 : R j) ≠ 0)
    (d e c : ℕ) (x : ∀ j, Fin d → R j) (y : ∀ j, Fin e → R j)
    (L : ∀ j, (Fin d → R j) →ₗ[R j] (Fin e → R j))
    (hx : VectorVanishes F R d x)
    (hclear : ∀ᶠ j in F, ((2 : R j) ^ c) • y j = L j (x j)) :
    ∀ k : Fin e, outerReduction F R (fun j => y j k) = 0 := by
  intro k
  apply (outerReduction_eq_zero_iff F R (fun j => y j k)).mpr
  intro n
  refine ((hx (c + n)).and hclear).mono ?_
  intro j hj
  obtain ⟨z, hz⟩ := hj.1
  have he : (2 : R j) ^ c * y j k = (L j (x j)) k :=
    congrFun hj.2 k
  have hm : (L j (x j)) k = (2 : R j) ^ (c + n) * (L j z) k :=
    congrFun ((congrArg (fun v => L j v) hz).trans ((L j).map_smul _ _)) k
  refine ⟨(L j z) k, mul_left_cancel₀ (pow_ne_zero c (two_ne_zero j)) ?_⟩
  calc
    _ = (2 : R j) ^ (c + n) * (L j z) k := he.trans hm
    _ = (2 : R j) ^ c * ((2 : R j) ^ n * (L j z) k) := by rw [pow_add, mul_assoc]

/-- Literal integral-contraction case of the previous theorem: c = 0. -/
theorem integral_defect_zero (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] [∀ j, IsDomain (R j)]
    (two_ne_zero : ∀ j, (2 : R j) ≠ 0)
    (d e : ℕ) (x : ∀ j, Fin d → R j)
    (L : ∀ j, (Fin d → R j) →ₗ[R j] (Fin e → R j))
    (hx : VectorVanishes F R d x) :
    ∀ k : Fin e, outerReduction F R (fun j => (L j (x j)) k) = 0 :=
  cleared_defect_zero F R two_ne_zero d e 0 x (fun j => L j (x j)) L hx
    (Filter.Eventually.of_forall (fun _ => by rw [pow_zero, one_smul]))

/-- The two sides of an actual retained identity agree in the outer
quotient when their difference is a cleared outer-small defect. -/
theorem cleared_identity_in_outer (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] [∀ j, IsDomain (R j)]
    (two_ne_zero : ∀ j, (2 : R j) ≠ 0)
    (d e c : ℕ) (x : ∀ j, Fin d → R j) (A B : ∀ j, Fin e → R j)
    (L : ∀ j, (Fin d → R j) →ₗ[R j] (Fin e → R j))
    (hx : VectorVanishes F R d x)
    (hclear : ∀ᶠ j in F, ((2 : R j) ^ c) • (A j - B j) = L j (x j)) :
    ∀ k : Fin e,
      outerReduction F R (fun j => A j k) = outerReduction F R (fun j => B j k) := by
  intro k
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact cleared_defect_zero F R two_ne_zero d e c x (fun j => A j - B j) L hx hclear k

/-- A nilpotent truncation cannot map its parameter to a unit in a
nonzero receiver, e.g. after localization at the prime (2). -/
theorem no_truncated_specialization {A B : Type*} [CommRing A] [CommRing B] [Nontrivial B]
    (f : A →+* B) (t : A) (n : ℕ) (ht : t ^ n = 0) (hu : IsUnit (f t)) : False := by
  have h : (f t) ^ n = 0 := by rw [← map_pow, ht, map_zero]
  exact not_isUnit_zero (h ▸ hu.pow n)

end PointwiseConverseOuterDefect
