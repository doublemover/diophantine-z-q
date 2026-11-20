module
public import CTFiniteResidueNorm318
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Trace.Basic
public section
noncomputable section

namespace CTPadicUnitNormHensel318

open Polynomial
open scoped Matrix

section MatrixLine

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι]

/-- The actual determinant of multiplication by 1+T y in the
specified integral basis. Its linear coefficient is the actual trace. -/
def line (b : Basis ι R S) (y : S) : R[X] :=
  Matrix.det (1 + (X : R[X]) • (Algebra.leftMulMatrix b y).map C)

theorem eval_line (b : Basis ι R S) (y : S) (t : R) :
    (line b y).eval t = Algebra.norm R (1 + t • y) := by
  rw [line,Algebra.norm_eq_matrix_det b]
  change (Polynomial.evalRingHom t) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  have rhs : Algebra.leftMulMatrix b (1 + t • y) = 1 + t • Algebra.leftMulMatrix b y := by
    simp only [map_add,map_one,map_smul]
  rw [rhs]
  ext i j
  by_cases hij : i=j <;>
    simp [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.add_apply,Matrix.one_apply,
      Matrix.smul_apply,smul_eq_mul,hij]

theorem derivative_line_zero (b : Basis ι R S) (y : S) :
    (line b y).derivative.eval 0 = Algebra.trace R S y := by
  rw [line,Matrix.derivative_det_one_add_X_smul,Algebra.trace_eq_matrix_trace b]

end MatrixLine

section Hensel

variable {p : ℕ} [Fact p.Prime]
variable {S ι : Type*} [CommRing S] [Algebra ℤ_[p] S] [IsLocalRing S]
  [IsLocalHom (algebraMap ℤ_[p] S)] [Fintype ι] [DecidableEq ι]

/-- A single p-adic Hensel lift of an approximate unit norm. The
direction y has trace a unit; it need not be 1 (trace(1) may vanish
mod p). The output is a genuine integral unit with exact norm. -/
theorem lift_unit_norm (b : Basis ι ℤ_[p] S) (a : ℤ_[p]ˣ) (u : Sˣ) (y : S)
    (hU : ‖Algebra.norm ℤ_[p] (u : S) - (a : ℤ_[p])‖ < 1)
    (hT : ‖Algebra.trace ℤ_[p] S y‖ = 1) :
    ∃ w : Sˣ, Units.map (Algebra.norm ℤ_[p] : S →* ℤ_[p]) w = a := by
  let n := Algebra.norm ℤ_[p] (u : S)
  let F : Polynomial ℤ_[p] := C n * line b y - C (a : ℤ_[p])
  have hN : ‖n‖ = 1 := PadicInt.norm_units (Units.map (Algebra.norm ℤ_[p]) u)
  have hf (t : ℤ_[p]) : F.aeval t = n * Algebra.norm ℤ_[p] (1 + t • y) - (a : ℤ_[p]) := by
    simp only [F,coe_aeval_eq_eval,eval_sub,eval_mul,eval_C,eval_line]
  have hd : F.derivative.aeval (0 : ℤ_[p]) = n * Algebra.trace ℤ_[p] S y := by
    simp only [F,derivative_sub,derivative_mul,derivative_C,zero_mul,zero_add,sub_zero,
      coe_aeval_eq_eval,eval_mul,eval_C,derivative_line_zero]
  have hdn : ‖F.derivative.aeval (0 : ℤ_[p])‖ = 1 := by rw [hd,norm_mul,hN,hT,mul_one]
  have h0 : ‖F.aeval (0 : ℤ_[p])‖ < ‖F.derivative.aeval (0 : ℤ_[p])‖ ^ 2 := by
    rw [hf,zero_smul,add_zero,map_one,mul_one,hdn,one_pow]
    exact hU
  obtain ⟨z,hz,hclose,_,_⟩ := hensels_lemma h0
  have hz1 : ‖z‖ < 1 := by simpa only [sub_zero,hdn] using hclose
  have hzM : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := PadicInt.not_isUnit_iff.2 hz1
  have hM : z • y ∈ IsLocalRing.maximalIdeal S := by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (map_nonunit (algebraMap ℤ_[p] S) z hzM)
  have hu1 : IsUnit (1 + z • y) := by
    apply (IsLocalRing.isUnit_or_isUnit_of_add_one
      (show (1 + z • y) + -(z • y) = 1 by simp)).resolve_right
    exact Ideal.neg_mem _ hM
  let w₁ := hu1.unit
  have hW₁ : (w₁ : S) = 1 + z • y := hu1.unit_spec
  refine ⟨u*w₁,Units.ext ?_⟩
  change Algebra.norm ℤ_[p] ((u : S) * (w₁ : S)) = (a : ℤ_[p])
  rw [map_mul,hW₁]
  exact sub_eq_zero.mp ((hf z).symm.trans hz)

/-- Consume the actual residue norm/trace comparison equations for the
chosen complete-DVR integral basis. Completeness/Hensel is proved here
using Mathlib; residue realization in a particular unramified local
extension is kept explicit rather than smuggled in as an arbitrary
isomorphism. -/
theorem unit_norm_surj_of_residue_comparisons
    (b : Basis ι ℤ_[p] S)
    {k l : Type*} [Field k] [Field l] [Fintype k] [Fintype l] [Algebra k l]
    (r : ℤ_[p] →+* k) (s : S →+* l)
    (hZero : ∀ x : ℤ_[p], r x = 0 ↔ ‖x‖ < 1)
    (hs : Function.Surjective s)
    (hsU : Function.Surjective (Units.map s.toMonoidHom))
    (hNorm : ∀ x : S, r (Algebra.norm ℤ_[p] x) = Algebra.norm k (s x))
    (hTrace : ∀ x : S, r (Algebra.trace ℤ_[p] S x) = Algebra.trace k l (s x)) :
    Function.Surjective (Units.map (Algebra.norm ℤ_[p] : S →* ℤ_[p])) := by
  intro a
  obtain ⟨u₀,hu₀⟩ := CTFiniteResidueNorm318.finite_field_unit_norm_surj k l
    (Units.map r.toMonoidHom a)
  obtain ⟨u,hu⟩ := hsU u₀
  have hU : ‖Algebra.norm ℤ_[p] (u : S) - (a : ℤ_[p])‖ < 1 := by
    apply (hZero _).1
    rw [map_sub,hNorm,sub_eq_zero]
    have h1 : s (u : S) = (u₀ : l) := congrArg Units.val hu
    have h2 : Algebra.norm k (u₀ : l) = r (a : ℤ_[p]) := congrArg Units.val hu₀
    rw [h1,h2]
  obtain ⟨y₀,hy₀⟩ := Algebra.trace_surjective (K := k) (L := l) (1 : k)
  obtain ⟨y,hy⟩ := hs y₀
  have ht1 : r (Algebra.trace ℤ_[p] S y) = 1 := by rw [hTrace,hy,hy₀]
  have hT : ‖Algebra.trace ℤ_[p] S y‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt fun h =>
      one_ne_zero (ht1.symm.trans ((hZero _).2 h)))
  exact lift_unit_norm b a u y hU hT

/-- An exact coordinate criterion for the same residue square. No
unramified field construction is implied by the coordinate premise. -/
theorem residue_matrix_of_coordinates (b : Basis ι ℤ_[p] S)
    [Algebra (ZMod p) (IsLocalRing.ResidueField S)]
    (c : Basis ι (ZMod p) (IsLocalRing.ResidueField S))
    (hBasis : ∀ j, IsLocalRing.residue S (b j) = c j)
    (hRepr : ∀ z : S, ∀ i, c.repr (IsLocalRing.residue S z) i = PadicInt.toZMod (b.repr z i))
    (x : S) :
    (Algebra.leftMulMatrix b x).map PadicInt.toZMod =
      Algebra.leftMulMatrix c (IsLocalRing.residue S x) := by
  ext i j
  simp only [Matrix.map_apply,Algebra.leftMulMatrix_apply,LinearMap.toMatrix_apply]
  change PadicInt.toZMod (b.repr (x * b j) i) =
    c.repr (IsLocalRing.residue S x * c j) i
  rw [← hBasis j,← map_mul,hRepr]

/-- The needed residue comparison is a single exact multiplication
matrix square on the integral basis and its residue basis. Source
uses literal residue of S and the pinned reduction ℤ_p → ZMod p. -/
theorem unit_norm_surj_of_residue_basis
    (b : Basis ι ℤ_[p] S)
    [Fintype (IsLocalRing.ResidueField S)]
    [Algebra (ZMod p) (IsLocalRing.ResidueField S)]
    (c : Basis ι (ZMod p) (IsLocalRing.ResidueField S))
    (hMatrix : ∀ x : S, (Algebra.leftMulMatrix b x).map PadicInt.toZMod =
      Algebra.leftMulMatrix c (IsLocalRing.residue S x)) :
    Function.Surjective (Units.map (Algebra.norm ℤ_[p] : S →* ℤ_[p])) := by
  let r : ℤ_[p] →+* ZMod p := PadicInt.toZMod
  let s := IsLocalRing.residue S
  have hZero (x : ℤ_[p]) : r x = 0 ↔ ‖x‖ < 1 := by
    rw [← RingHom.mem_ker,show r.ker = IsLocalRing.maximalIdeal ℤ_[p] from PadicInt.ker_toZMod]
    exact PadicInt.not_isUnit_iff
  have hsU : Function.Surjective (Units.map s.toMonoidHom) := by
    intro x
    obtain ⟨y,hy⟩ := IsLocalRing.residue_surjective (x : IsLocalRing.ResidueField S)
    have hY : IsUnit y := (IsLocalRing.residue_ne_zero_iff_isUnit y).1 (fun h0 => x.ne_zero (hy.symm.trans h0))
    refine ⟨hY.unit,Units.ext ?_⟩
    change s (hY.unit : S) = (x : IsLocalRing.ResidueField S)
    rw [hY.unit_spec,hy]
  apply unit_norm_surj_of_residue_comparisons b r s hZero IsLocalRing.residue_surjective hsU
  · intro x
    rw [Algebra.norm_eq_matrix_det b,Algebra.norm_eq_matrix_det c,RingHom.map_det]
    exact congrArg Matrix.det (hMatrix x)
  · intro x
    rw [Algebra.trace_eq_matrix_trace b,Algebra.trace_eq_matrix_trace c,← hMatrix]
    simp [Matrix.trace,r]

end Hensel
end CTPadicUnitNormHensel318
