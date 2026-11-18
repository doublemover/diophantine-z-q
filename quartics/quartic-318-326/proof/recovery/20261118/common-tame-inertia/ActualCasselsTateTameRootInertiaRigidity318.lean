module
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public section

/-! Kernel rigidity for a selected tame unit-root coefficient field.
No Henselianity, normality of the selected field, or splitting of a
restriction of automorphism groups is used. -/

namespace ActualCasselsTateTameRootInertiaRigidity318
open Polynomial
open scoped BigOperators

section Rigidity
variable {A k : Type*} [CommRing A] [IsDomain A] [Field k]

/-- Two nonzero-residue roots in the same tame power fiber cannot
coalesce on reduction. The target reduction need not be injective. -/
theorem tame_roots_eq (red : A →+* k) (n : ℕ) (hn : (n : k) ≠ 0)
    {x y : A} (hp : x ^ n = y ^ n) (hr : red x = red y) (hy : red y ≠ 0) :
    x = y := by
  let D := ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)
  have hred : red D = (n : k) * (red y) ^ (n - 1) := by
    simp only [D, map_sum, map_mul, map_pow, hr, geom_sum₂_self]
  have hD : D ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hred
    exact (mul_ne_zero hn (pow_ne_zero _ hy)) hred.symm
  have hprod : D * (x - y) = 0 := by
    calc
      _ = x ^ n - y ^ n := geom_sum₂_mul x y n
      _ = 0 := sub_eq_zero.mpr hp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hD)
end Rigidity

section Adjoin
variable {R A k : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field k]
variable (n : ℕ) (u : Rˣ)
local notation "p" => ((X : R[X]) ^ n - C (u : R))
local notation "S" => AdjoinRoot p
local notation "t" => AdjoinRoot.root p

lemma root_power_eq : t ^ n = AdjoinRoot.of p (u : R) := by
  have h := AdjoinRoot.eval₂_root p
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h

/-- Comparing actions on the old integer ring and on just the REDUCTION
of the adjoined root suffices to compare them on all of the root algebra.
The nonzero residue of the root follows from the defining unit. -/
theorem tame_root_homs_eq (red : A →+* k) (hn : (n : k) ≠ 0)
    (f g : S →+* A) (hR : f.comp (AdjoinRoot.of p) = g.comp (AdjoinRoot.of p))
    (ht : red (f t) = red (g t)) : f = g := by
  apply AdjoinRoot.ringHom_ext hR
  have hp : (f t) ^ n = (g t) ^ n := by
    rw [← map_pow, ← map_pow, root_power_eq]
    exact RingHom.congr_fun hR (u : R)
  refine tame_roots_eq red n hn hp ht ?_
  intro hz
  have hunit : IsUnit (red (g (AdjoinRoot.of p (u : R)))) :=
    ((u.isUnit.map (AdjoinRoot.of p)).map g).map red
  have hn' : n ≠ 0 := by
    intro h
    apply hn
    simp [h]
  rw [← root_power_eq n u, map_pow, map_pow, hz, zero_pow hn'] at hunit
  exact hunit.ne_zero rfl
end Adjoin

section Localized
variable {R A k : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field k]
variable (n : ℕ) (u : Rˣ)
local notation "p" => ((X : R[X]) ^ n - C (u : R))
local notation "S" => AdjoinRoot p
variable (P : Ideal S) [P.IsPrime]
local notation "T" => Localization.AtPrime P
local notation "j" => algebraMap S T
local notation "t" => AdjoinRoot.root p

/-- Compare maps on any chosen local factor, not on a falsely assumed
integral or irreducible global root algebra. -/
theorem tame_local_homs_eq (red : A →+* k) (hn : (n : k) ≠ 0)
    (f g : T →+* A)
    (hR : (f.comp j).comp (AdjoinRoot.of p) = (g.comp j).comp (AdjoinRoot.of p))
    (ht : red (f (j t)) = red (g (j t))) : f = g := by
  apply IsLocalization.ringHom_ext P.primeCompl
  exact tame_root_homs_eq n u red hn (f.comp j) (g.comp j) hR ht

/-- For two residual-identity actions on a common integer ring, only
agreement on the old integer coefficients is needed. In particular a
kernel element fixes the entire embedded selected integer ring. -/
theorem inertia_agrees_on_selected (red : A →+* k) (hn : (n : k) ≠ 0)
    (i : T →+* A) (a b : A →+* A)
    (ha : ∀ x, red (a x) = red x) (hb : ∀ x, red (b x) = red x)
    (hR : ∀ r : R, a (i (j (AdjoinRoot.of p r))) = b (i (j (AdjoinRoot.of p r)))) :
    a.comp i = b.comp i := by
  apply tame_local_homs_eq n u P red hn
  · exact RingHom.ext hR
  · exact (ha _).trans (hb _).symm

/-- Equality persists on the whole selected fraction field, provided
the proposed field embeddings restrict to the displayed integer maps.
Neither surjectivity of inertia restriction nor the existence of the
common normal field/place is a hypothesis hidden in this equality. -/
theorem inertia_agrees_on_selected_field [IsDomain T] {N : Type*} [Field N]
    (red : A →+* k) (hn : (n : k) ≠ 0)
    (i : T →+* A) (a b : A →+* A)
    (ha : ∀ x, red (a x) = red x) (hb : ∀ x, red (b x) = red x)
    (hR : ∀ r : R, a (i (j (AdjoinRoot.of p r))) = b (i (j (AdjoinRoot.of p r))))
    (v : A →+* N) (f g : FractionRing T →+* N)
    (hf : f.comp (algebraMap T (FractionRing T)) = v.comp (a.comp i))
    (hg : g.comp (algebraMap T (FractionRing T)) = v.comp (b.comp i)) :
    f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors T)
  rw [hf, hg, inertia_agrees_on_selected n u P red hn i a b ha hb hR]
end Localized
end ActualCasselsTateTameRootInertiaRigidity318
