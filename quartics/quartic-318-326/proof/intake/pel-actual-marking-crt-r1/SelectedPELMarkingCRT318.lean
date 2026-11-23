module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.ZMod.Basic

public section

namespace SelectedPELMarkingCRT318

/-- The full kernel of the specified integer multiplication on the input
point group, not an independently chosen copy of its torsion. -/
@[expose] def torsion (A : Type*) [AddCommGroup A] (n : ℤ) : AddSubgroup A where
  carrier := {x | n • x = 0}
  zero_mem' := smul_zero n
  add_mem' := by
    intro x y hx hy
    change n • (x + y) = 0
    change n • x = 0 at hx
    change n • y = 0 at hy
    rw [smul_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    change n • (-x) = 0
    change n • x = 0 at hx
    rw [zsmul_neg, hx, neg_zero]

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem killed {n : ℤ} (x : torsion A n) : n • x.val = 0 := x.property

private theorem scale_pair (a b c d : ℤ) (h : a * b = c * d) (x : A) :
    a • (b • x) = c • (d • x) :=
  (mul_smul a b x).symm.trans ((congrArg (fun z : ℤ => z • x) h).trans (mul_smul c d x))

private theorem scale_residue (a b c k : ℤ) (h : a * b = c * k + 1)
    (x : A) (hx : k • x = 0) : a • (b • x) = x := by
  rw [← mul_smul, h, add_smul, mul_smul, hx, smul_zero, one_smul, zero_add]

/-- The original divisibility convention: restrict the order-33 frame by [11]. -/
@[expose] def downThree : torsion A 33 →+ torsion A 3 where
  toFun x := ⟨(11 : ℤ) • x.val, by
    change (3 : ℤ) • ((11 : ℤ) • x.val) = 0
    exact (scale_pair 3 11 1 33 (by decide) x.val).trans
      ((one_smul ℤ ((33 : ℤ) • x.val)).trans (killed x))⟩
  map_zero' := Subtype.ext (smul_zero (11 : ℤ))
  map_add' x y := Subtype.ext (smul_add (11 : ℤ) x.val y.val)

/-- Restrict the same order-33 frame by [3]. -/
@[expose] def downEleven : torsion A 33 →+ torsion A 11 where
  toFun x := ⟨(3 : ℤ) • x.val, by
    change (11 : ℤ) • ((3 : ℤ) • x.val) = 0
    exact (scale_pair 11 3 1 33 (by decide) x.val).trans
      ((one_smul ℤ ((33 : ℤ) • x.val)).trans (killed x))⟩
  map_zero' := Subtype.ext (smul_zero (3 : ℤ))
  map_add' x y := Subtype.ext (smul_add (3 : ℤ) x.val y.val)

/-- Katz/Tate divisibility normalization: 2 times the actual third point
minus 7 times the actual eleventh point, in the same ambient group. -/
@[expose] def combine (p : torsion A 3) (q : torsion A 11) : torsion A 33 :=
  ⟨(2 : ℤ) • p.val + (-7 : ℤ) • q.val, by
    change (33 : ℤ) • ((2 : ℤ) • p.val + (-7 : ℤ) • q.val) = 0
    rw [smul_add, scale_pair 33 2 22 3 (by decide) p.val,
      scale_pair 33 (-7) (-21) 11 (by decide) q.val,
      killed p, killed q, smul_zero, smul_zero, add_zero]⟩

theorem downThree_combine (p : torsion A 3) (q : torsion A 11) :
    downThree (combine p q) = p := by
  apply Subtype.ext
  change (11 : ℤ) • ((2 : ℤ) • p.val + (-7 : ℤ) • q.val) = p.val
  rw [smul_add, scale_residue 11 2 7 3 (by decide) p.val (killed p),
    scale_pair 11 (-7) (-7) 11 (by decide) q.val, killed q, smul_zero, add_zero]

theorem downEleven_combine (p : torsion A 3) (q : torsion A 11) :
    downEleven (combine p q) = q := by
  apply Subtype.ext
  change (3 : ℤ) • ((2 : ℤ) • p.val + (-7 : ℤ) • q.val) = q.val
  rw [smul_add, scale_pair 3 2 2 3 (by decide) p.val, killed p, smul_zero,
    scale_residue 3 (-7) (-2) 11 (by decide) q.val (killed q), zero_add]

theorem combine_down (x : torsion A 33) :
    combine (downThree x) (downEleven x) = x := by
  apply Subtype.ext
  change (2 : ℤ) • ((11 : ℤ) • x.val) + (-7 : ℤ) • ((3 : ℤ) • x.val) = x.val
  calc
    _ = ((2 * 11 + (-7) * 3 : ℤ)) • x.val := by rw [add_smul, mul_smul, mul_smul]
    _ = (1 : ℤ) • x.val := congrArg (fun z : ℤ => z • x.val) (by decide)
    _ = x.val := one_smul ℤ _

/-- This is an actual equivalence of the full torsion kernels. -/
@[expose] def split33 : torsion A 33 ≃+ torsion A 3 × torsion A 11 where
  toFun x := (downThree x, downEleven x)
  invFun x := combine x.1 x.2
  left_inv := combine_down
  right_inv x := Prod.ext (downThree_combine x.1 x.2) (downEleven_combine x.1 x.2)
  map_add' x y := Prod.ext (downThree.map_add x y) (downEleven.map_add x y)

/-- Naturality for every additive endomorphism, including the actual original
left order action or a marked comparison on the given point groups. -/
theorem combine_natural (f : A →+ B) (p : torsion A 3) (q : torsion A 11) :
    f (combine p q).val = (2 : ℤ) • f p.val + (-7 : ℤ) • f q.val := by
  change f ((2 : ℤ) • p.val + (-7 : ℤ) • q.val) = _
  simp only [map_add, map_zsmul]

section Markings

variable {R33 R3 R11 : Type*} [Ring R33] [Ring R3] [Ring R11]
variable (reduce : R33 ≃+* R3 × R11)
    (markThree : R3 ≃+ torsion A 3) (markEleven : R11 ≃+ torsion A 11)

/-- For the actual ring reductions, assemble the two actual frames into a
full frame, without supplying a separate level-33 bijection. -/
@[expose] def marked33 : R33 ≃+ torsion A 33 :=
  reduce.toAddEquiv.trans ((markThree.prodCongr markEleven).trans split33.symm)

theorem marked33_downThree (x : R33) :
    downThree (marked33 reduce markThree markEleven x) = markThree (reduce x).1 :=
  downThree_combine _ _

theorem marked33_downEleven (x : R33) :
    downEleven (marked33 reduce markThree markEleven x) = markEleven (reduce x).2 :=
  downEleven_combine _ _

/-- Send the right multiplier through actual ring reduction without switching
its order. In particular this holds when g is the value of a frame unit. -/
theorem marked33_right (x g : R33) :
    marked33 reduce markThree markEleven (x * g) =
      combine (markThree ((reduce x).1 * (reduce g).1))
        (markEleven ((reduce x).2 * (reduce g).2)) := by
  change combine (markThree (reduce (x * g)).1) (markEleven (reduce (x * g)).2) = _
  exact congrArg (fun y : R3 × R11 => combine (markThree y.1) (markEleven y.2))
    (map_mul reduce x g)

/-- The common original left action survives assembly, with the same
additive endomorphism acting on both actual component marks. -/
theorem marked33_left_of_components (f : A →+ A) (a x : R33)
    (h3 : f (markThree (reduce x).1).val =
      (markThree ((reduce a).1 * (reduce x).1)).val)
    (h11 : f (markEleven (reduce x).2).val =
      (markEleven ((reduce a).2 * (reduce x).2)).val) :
    f (marked33 reduce markThree markEleven x).val =
      (marked33 reduce markThree markEleven (a * x)).val := by
  change f (combine (markThree (reduce x).1) (markEleven (reduce x).2)).val =
    (combine (markThree (reduce (a * x)).1) (markEleven (reduce (a * x)).2)).val
  rw [combine_natural, h3, h11, map_mul]

end Markings

/-- In one actual order-33 lattice coordinate, the raw sum fails both true
divisibility restrictions on the nonzero third and eleventh points. -/
theorem raw_sum_fails :
    (11 : ℤ) • ((11 : ZMod 33) + 3) ≠ (11 : ZMod 33) ∧
    (3 : ℤ) • ((11 : ZMod 33) + 3) ≠ (3 : ZMod 33) := by decide

end SelectedPELMarkingCRT318

#print axioms SelectedPELMarkingCRT318.split33
#print axioms SelectedPELMarkingCRT318.marked33_right
#print axioms SelectedPELMarkingCRT318.raw_sum_fails
