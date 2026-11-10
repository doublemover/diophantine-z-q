module
public import OriginalPrincipalUniformClearing318
public import Mathlib.Tactic.Ring
public section
noncomputable section
namespace OriginalPrincipalCocycleRows318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite OriginalPrincipalLocalization318
universe u v
variable (X : Scheme.{u}) {ι : Type v} [Fintype ι] (f : ι → Γ(X,⊤))
abbrev U (i : ι) := X.basicOpen (f i)
abbrev V (i j : ι) := U X f i ⊓ U X f j
abbrev W (i j k : ι) := U X f i ⊓ V X f j k
abbrev left (i j : ι) : V X f i j ≤ U X f i := inf_le_left
abbrev right (i j : ι) : V X f i j ≤ U X f j := inf_le_right
abbrev tripleLeft (i j k : ι) : W X f i j k ≤ V X f i j :=
  le_inf inf_le_left (inf_le_right.trans inf_le_left)
abbrev tripleRight (i j k : ι) : W X f i j k ≤ V X f j k := inf_le_right
abbrev tripleOuter (i j k : ι) : W X f i j k ≤ V X f i k :=
  le_inf inf_le_left (inf_le_right.trans inf_le_right)

/-- Actual original additive Čech equation on the whole triple intersection. -/
def Cocycle (c : ∀ i j, Γ(X,V X f i j)) : Prop := ∀ i j k,
  res X (tripleLeft X f i j k) (c i j) + res X (tripleRight X f i j k) (c j k) =
    res X (tripleOuter X f i j k) (c i k)

variable [hX : IsAffine X]
lemma affine_U (i : ι) : IsAffineOpen (U X f i) := (isAffineOpen_top X).basicOpen _
lemma affine_V (i j : ι) : IsAffineOpen (V X f i j) := by
  have h := (isAffineOpen_top X).basicOpen (f i * f j)
  simpa only [Scheme.basicOpen_mul] using h

include hX in
/-- Clear an entire cocycle row, then kill its finite family of descent
errors on the ORIGINAL double intersections. The resulting row differences
hold before localization, even when the coefficient has torsion. -/
theorem row (c : ∀ i j, Γ(X,V X f i j)) (hc : Cocycle X f c) (i : ι) :
    ∃ n : ℕ, ∃ a : ∀ j, Γ(X,U X f j), ∀ j k,
      res X (right X f j k) (a k) - res X (left X f j k) (a j) =
        (coefficient X (V X f j k) (f i))^n * c j k := by
  classical
  obtain ⟨n,a,ha⟩ := OriginalPrincipalUniformClearing318.clear_family X
    (U X f) (affine_U X f) (f i) (c i)
  let d (j k : ι) : Γ(X,V X f j k) :=
    res X (right X f j k) (a k) - res X (left X f j k) (a j) -
      (coefficient X (V X f j k) (f i))^n * c j k
  have hd (j k : ι) : res X (tripleRight X f i j k) (d j k) = 0 := by
    have hj := congrArg (res X (tripleLeft X f i j k)) (ha j)
    have hk := congrArg (res X (tripleOuter X f i j k)) (ha k)
    simp only [map_mul,map_pow,res_coefficient,res_res] at hj hk
    dsimp [d]
    simp only [map_sub,map_mul,map_pow,res_coefficient,res_res]
    rw [← hj,← hk,← hc i j k]
    ring
  obtain ⟨m,hm⟩ := OriginalPrincipalUniformClearing318.kill_family X
    (fun p : ι × ι => V X f p.1 p.2)
    (fun p => affine_V X f p.1 p.2) (f i)
    (fun p => d p.1 p.2) (fun p => hd p.1 p.2)
  refine ⟨m+n,fun j => (coefficient X (U X f j) (f i))^m * a j,fun j k => ?_⟩
  rw [map_mul,map_pow,res_coefficient,map_mul,map_pow,res_coefficient]
  calc
    _ = (coefficient X (V X f j k) (f i))^(m+n) * c j k +
        (coefficient X (V X f j k) (f i))^m * d j k := by
      dsimp [d]
      rw [pow_add]
      ring
    _ = _ := by rw [hm (j,k),add_zero]

include hX in
/-- One common exponent works for every row, with all row sections still
living on their unchanged original principal opens. -/
theorem rows (c : ∀ i j, Γ(X,V X f i j)) (hc : Cocycle X f c) :
    ∃ n : ℕ, ∃ a : ∀ i j, Γ(X,U X f j), ∀ i j k,
      res X (right X f j k) (a i k) - res X (left X f j k) (a i j) =
        (coefficient X (V X f j k) (f i))^n * c j k := by
  classical
  choose n a ha using fun i => row X f c hc i
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N,fun i j => (coefficient X (U X f j) (f i))^(N-n i) * a i j,fun i j k => ?_⟩
  rw [map_mul,map_pow,res_coefficient,map_mul,map_pow,res_coefficient,← mul_sub,ha]
  rw [← mul_assoc,← pow_add,Nat.sub_add_cancel (hn i)]
end OriginalPrincipalCocycleRows318
