module
public import SquarefreeTernaryLatticeCover318
public section
noncomputable section
namespace TriangularTernaryBasis318
open TernaryQuadraticLineCover318
set_option maxHeartbeats 1000000

/-- The exact mixed-chart congruences; q is the finite-slope modulus,
r the infinity modulus, and q*r the original squarefree modulus. -/
@[expose] def Conditions (q r A B : ℤ) (v : Vector ℤ) : Prop :=
  r∣v.1 ∧ q∣v.2.1-A*v.1 ∧ q*r∣v.2.2-B*v.1

@[expose] def basisMap (q r A B : ℤ) : Vector ℤ →+ Vector ℤ where
  toFun u := (r*u.1,A*r*u.1+q*u.2.1,B*r*u.1+q*r*u.2.2)
  map_zero' := by simp
  map_add' u v := by
    apply Prod.ext
    · dsimp; ring
    · apply Prod.ext <;> dsimp <;> ring

/-- Actual integer coordinates in the triangular generators, not a rational
basis that might span a proper sublattice. -/
theorem conditions_iff_image (q r A B : ℤ) (v : Vector ℤ) :
    Conditions q r A B v ↔ ∃ u : Vector ℤ, basisMap q r A B u=v := by
  rcases v with ⟨x,z,w⟩
  constructor
  · rintro ⟨⟨X,hX⟩,⟨Z,hZ⟩,⟨W,hW⟩⟩
    refine ⟨(X,Z,W),?_⟩
    apply Prod.ext
    · exact hX.symm
    · apply Prod.ext
      · change A*r*X+q*Z=z
        rw [←hZ,hX]
        ring
      · change B*r*X+q*r*W=w
        rw [←hW,hX]
        ring
  · rintro ⟨u,rfl⟩
    refine ⟨⟨u.1,rfl⟩,⟨u.2.1,?_⟩,⟨u.2.2,?_⟩⟩
    · dsimp [basisMap]
      ring
    · dsimp [basisMap]
      ring

lemma basisMap_injective (q r A B : ℤ) (hq : q≠0) (hr : r≠0) :
    Function.Injective (basisMap q r A B) := by
  intro u v he
  have hx : r*u.1=r*v.1 := congrArg Prod.fst he
  have hX : u.1=v.1 := mul_left_cancel₀ hr hx
  have hz : A*r*u.1+q*u.2.1=A*r*v.1+q*v.2.1 := congrArg (fun z : Vector ℤ => z.2.1) he
  have hw : B*r*u.1+q*r*u.2.2=B*r*v.1+q*r*v.2.2 := congrArg (fun z : Vector ℤ => z.2.2) he
  rw [hX] at hz hw
  have hZ : u.2.1=v.2.1 := mul_left_cancel₀ hq (add_left_cancel hz)
  have hW : u.2.2=v.2.2 := mul_left_cancel₀ (mul_ne_zero hq hr) (add_left_cancel hw)
  exact Prod.ext hX (Prod.ext hZ hW)

/-- Every congruence vector has unique integral coefficients in the three
explicit generators (r,Ar,Br), (0,q,0), (0,0,qr). -/
theorem unique_coordinates (q r A B : ℤ) (hq : q≠0) (hr : r≠0)
    (v : Vector ℤ) (hv : Conditions q r A B v) :
    ∃! u : Vector ℤ, basisMap q r A B u=v := by
  obtain ⟨u,hu⟩ := (conditions_iff_image q r A B v).mp hv
  exact ⟨u,hu,fun w hw => basisMap_injective q r A B hq hr (hw.trans hu.symm)⟩

@[expose] def first (r A B : ℤ) : Vector ℤ := (r,A*r,B*r)
@[expose] def second (q : ℤ) : Vector ℤ := (0,q,0)
@[expose] def third (q r : ℤ) : Vector ℤ := (0,0,q*r)
@[expose] def Within (M : ℤ) (v : Vector ℤ) : Prop := |v.1|≤M ∧ |v.2.1|≤M ∧ |v.2.2|≤M

/-- Least nonnegative finite-chart representatives produce an actual
basis in the coordinate box [-qr,qr]^3. This is not a reduced-basis or
all-successive-minima assertion. -/
theorem basis_box_bound (q r A B : ℤ) (hq : 0<q) (hr : 0<r)
    (hA0 : 0≤A) (hA : A<q) (hB0 : 0≤B) (hB : B<q) :
    Within (q*r) (first r A B) ∧ Within (q*r) (second q) ∧ Within (q*r) (third q r) := by
  have hq1 : 1≤q := by omega
  have hr1 : 1≤r := by omega
  have hqr : 0≤q*r := mul_nonneg (le_of_lt hq) (le_of_lt hr)
  have hAr : 0≤A*r := mul_nonneg hA0 (le_of_lt hr)
  have hBr : 0≤B*r := mul_nonneg hB0 (le_of_lt hr)
  have hArb : A*r≤q*r := mul_le_mul_of_nonneg_right (le_of_lt hA) (le_of_lt hr)
  have hBrb : B*r≤q*r := mul_le_mul_of_nonneg_right (le_of_lt hB) (le_of_lt hr)
  simp only [Within,first,second,third,abs_of_nonneg (le_of_lt hr),abs_of_nonneg (le_of_lt hq),
    abs_of_nonneg hAr,abs_of_nonneg hBr,abs_of_nonneg hqr,abs_zero]
  constructor
  · exact ⟨by nlinarith,hArb,hBrb⟩
  · exact ⟨⟨hqr,by nlinarith,hqr⟩,⟨hqr,hqr,le_rfl⟩⟩

end TriangularTernaryBasis318
