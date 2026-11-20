module
public import ActualOldKummerRelativeLift318
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

open scoped BigOperators

public section

namespace ActualCCLRetainedH22Boundary318
open ActualOldKummerRelativeLift318

variable {Γ M W : Type*} [Group Γ] [AddCommGroup M]
variable {U0 U1 V0 V1 : W → Type*}
variable [∀ w, AddCommGroup (U0 w)] [∀ w, AddCommGroup (U1 w)]
variable [∀ w, AddCommGroup (V0 w)] [∀ w, AddCommGroup (V1 w)]

/-- The same supported finite degree-zero Kummer boundary as in
ActualGlobalTraceTorsionSupported318. -/
@[expose] def groupBoundary (ρ : Γ →* AddMonoid.End M) (v : M) : Γ → M :=
  fun g => ρ g v - v

/-- Data of the actual nonnegative H22 models in degrees 0,1.
The loc maps are retained maps, not substitutions into H¹. -/
structure LocalData (ρ : Γ →* AddMonoid.End M) where
  dU : (w : W) → U0 w →+ U1 w
  dV : (w : W) → V0 w →+ V1 w
  i0 : (w : W) → U0 w →+ V0 w
  i1 : (w : W) → U1 w →+ V1 w
  loc0 : (w : W) → M →+ V0 w
  loc1 : (w : W) → (Γ → M) →+ V1 w
  map_i : ∀ w x, dV w (i0 w x) = i1 w (dU w x)
  map_loc : ∀ w v, dV w (loc0 w v) = loc1 w (groupBoundary ρ v)
  exact_1 : ∀ w (u : U1 w), (∃ v : V0 w, dV w v = i1 w u) → ∃ x, dU w x = u
  onto_0 : ∀ w (v : V0 w), dV w v = 0 → ∃ x, dU w x = 0 ∧ i0 w x = v
  inject_0 : ∀ w (x : U0 w), dU w x = 0 → i0 w x = 0 → x = 0

abbrev Degree0 (M : Type*) (U0 : W → Type*) := M × ((w : W) → U0 w)
abbrev Degree1 (Γ M : Type*) (U1 V0 : W → Type*) :=
  (Γ → M) × (((w : W) → U1 w) × ((w : W) → V0 w))

/-- Literal shifted-cone d⁰: no degree -1 local term is introduced.
Its last component is loc₀−i₀, in the original H22 sign convention. -/
@[expose] def relativeBoundary (ρ : Γ →* AddMonoid.End M)
    (A : LocalData (U0:=U0) (U1:=U1) (V0:=V0) (V1:=V1) ρ)
    (x : Degree0 M U0) : Degree1 Γ M U1 V0 :=
  (groupBoundary ρ x.1,
    (fun w => A.dU w (x.2 w)), (fun w => A.loc0 w x.1 - A.i0 w (x.2 w)))

/-- Recover the literal whole-cone primitive with this same supported
global component. The original local cycles and degree-zero
corrections stay in the equality, including their torsion parts. -/
theorem retain_all_H22 (ρ : Γ →* AddMonoid.End M)
    (A : LocalData (U0:=U0) (U1:=U1) (V0:=V0) (V1:=V1) ρ)
    (m : ℕ) (v : M)
    (p : Γ → M) (u : (w : W) → U1 w) (q : (w : W) → V0 w)
    (hv : ∀ g, m • p g = ρ g v - v)
    (hH22 : ∀ w, A.dV w (q w) = A.loc1 w p - A.i1 w (u w)) :
    ∃ w0 : (w : W) → U0 w,
      relativeBoundary ρ A (v,w0) = m • ((p,u,q) : Degree1 Γ M U1 V0) := by
  have hp : m • p = groupBoundary ρ v := by
    funext g
    simpa only [Pi.smul_apply, groupBoundary] using hv g
  have hq (w : W) : A.dV w (m • q w) =
      A.dV w (A.loc0 w v) - A.i1 w (m • u w) := by
    calc
      _ = m • (A.loc1 w p - A.i1 w (u w)) := by rw [map_nsmul, hH22]
      _ = A.loc1 w (m • p) - A.i1 w (m • u w) := by simp only [nsmul_sub, map_nsmul]
      _ = _ := by rw [hp, A.map_loc]
  have hx (w : W) : ∃ x, A.dU w x = m • u w ∧ A.i0 w x = A.loc0 w v - m • q w :=
    (lift_same_global_entry (A.dU w) (A.dV w) (A.i0 w) (A.i1 w)
      (A.map_i w) (A.exact_1 w) (A.onto_0 w) (A.inject_0 w)
      (A.loc0 w v) (A.loc0 w v) (m • q w) (m • u w) rfl (hq w)).exists
  let x0 (w : W) : U0 w := Classical.choose (hx w)
  have hX (w : W) := Classical.choose_spec (hx w)
  refine ⟨x0, ?_⟩
  apply Prod.ext
  · simpa only [relativeBoundary, Prod.smul_fst] using hp.symm
  · apply Prod.ext
    · funext w
      simpa only [relativeBoundary, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, x0] using (hX w).1
    · funext w
      simp only [relativeBoundary, Prod.smul_snd, Pi.smul_apply]
      change A.loc0 w v - A.i0 w (Classical.choose (hx w)) = m • q w
      rw [(hX w).2]
      abel

/-- Compare the actual two retained H22 representatives, with the
literal signed split norm coefficient e (at this center a_r - 2).
Neither of their chosen local corrections is reselected. -/
theorem retain_signed_H22_difference (ρ : Γ →* AddMonoid.End M)
    (A : LocalData (U0:=U0) (U1:=U1) (V0:=V0) (V1:=V1) ρ)
    (e : ℤ) (v : M) (p p' : Γ → M)
    (u u' : (w : W) → U1 w) (q q' : (w : W) → V0 w)
    (hv : ∀ g, p' g - e • p g = ρ g v - v)
    (hH22 : ∀ w, A.dV w (q w) = A.loc1 w p - A.i1 w (u w))
    (hH22' : ∀ w, A.dV w (q' w) = A.loc1 w p' - A.i1 w (u' w)) :
    ∃ w0 : (w : W) → U0 w,
      relativeBoundary ρ A (v,w0) =
        (p' - e • p, (fun w => u' w - e • u w), (fun w => q' w - e • q w)) := by
  have hq (w : W) : A.dV w (q' w - e • q w) =
      A.loc1 w (p' - e • p) - A.i1 w (u' w - e • u w) := by
    simp only [map_sub, map_zsmul, hH22, hH22', zsmul_sub]
    abel
  have hp (g : Γ) : (1 : ℕ) • (p' - e • p) g = ρ g v - v := by
    simpa only [one_nsmul, Pi.sub_apply, Pi.smul_apply] using hv g
  simpa only [one_nsmul] using retain_all_H22 ρ A 1 v (p' - e • p)
    (fun w => u' w - e • u w) (fun w => q' w - e • q w) hp hq

section Compression

variable {C0 C1 I J R : Type*} [AddCommGroup C0] [AddCommGroup C1]
variable [Fintype I] [CommRing R]

/-- Actual compression carries that very primitive, yielding the exact
matrix identity required at each common finite stage. Merely finding a
survivor or using equal ranks would not provide hD and hz. -/
theorem retained_matrix_boundary (D : C0 → C1)
    (project0 : C0 →+ (I → R)) (project1 : C1 →+ (J → R))
    (d : J → I → R) (z : J → R)
    (hD : ∀ v j, project1 (D v) j = ∑ i, d j i * project0 v i)
    (p : C1) (hz : project1 p = z) (m : ℕ) (v : C0) (hV : D v = m • p) :
    ∀ j, (m : R) * z j = ∑ i, d j i * project0 v i := by
  intro j
  have h := hD v j
  rw [hV, map_nsmul, hz, Pi.smul_apply, nsmul_eq_mul] at h
  exact h

variable {X2 X3 Y0 Y1 B : Type*}
variable [AddCommGroup X2] [AddCommGroup X3] [AddCommGroup Y0] [AddCommGroup Y1] [AddCommGroup B]

/-- The actual paired trace sees the SAME transported degree-zero
primitive, when the labelled comparison is genuinely a chain map.
The minus sign is the compact cup Leibniz sign, not an extra
Heegner multiplier or derivative-normalization factor. -/
theorem paired_boundary_from_same_primitive (D : C0 → C1)
    (dX : X2 →+ X3) (dY : Y0 →+ Y1)
    (lift0 : C0 →+ Y0) (lift1 : C1 →+ Y1)
    (map_d : ∀ v, lift1 (D v) = dY (lift0 v))
    (P21 : X2 →+ Y1 →+ B) (P30 : X3 →+ Y0 →+ B)
    (leibniz : ∀ x v, P30 (dX x) v + P21 x (dY v) = 0)
    (p : C1) (m : ℕ) (v : C0) (hV : D v = m • p) (x : X2) :
    m • P21 x (lift1 p) = - P30 (dX x) (lift0 v) := by
  have hy : m • lift1 p - 0 = dY (lift0 v) := by
    rw [sub_zero, ← map_nsmul, ← hV, map_d]
  have h := paired_row_diff_at dX dY P21 P30 leibniz _ 0 (lift0 v) hy x
  simpa only [map_zero, sub_zero, map_nsmul] using h

/-- On the same signed norm comparison its actual transported
primitive gives the literal paired coboundary incidence, for every
test cochain x, not just a cycle. This is the row used before the
original ordered Schur elimination. -/
theorem paired_signed_difference (D : C0 → C1)
    (dX : X2 →+ X3) (dY : Y0 →+ Y1)
    (lift0 : C0 →+ Y0) (lift1 : C1 →+ Y1)
    (map_d : ∀ v, lift1 (D v) = dY (lift0 v))
    (P21 : X2 →+ Y1 →+ B) (P30 : X3 →+ Y0 →+ B)
    (leibniz : ∀ x v, P30 (dX x) v + P21 x (dY v) = 0)
    (p p' : C1) (e : ℤ) (v : C0) (hV : D v = p' - e • p) (x : X2) :
    P21 x (lift1 p') - e • P21 x (lift1 p) = - P30 (dX x) (lift0 v) := by
  have hy : lift1 p' - e • lift1 p = dY (lift0 v) := by
    rw [← map_zsmul, ← map_sub, ← hV, map_d]
  have h := paired_row_diff_at dX dY P21 P30 leibniz _ _ (lift0 v) hy x
  simpa only [map_zsmul] using h

end Compression

end ActualCCLRetainedH22Boundary318

#print axioms ActualCCLRetainedH22Boundary318.retain_all_H22
#print axioms ActualCCLRetainedH22Boundary318.retained_matrix_boundary
#print axioms ActualCCLRetainedH22Boundary318.paired_signed_difference
