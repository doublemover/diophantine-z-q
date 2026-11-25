module
public import OriginalUpperActualFibreIncidence318
public import OriginalUpperGenerizationField318
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Length

public section
noncomputable section
namespace OriginalUpperActualFibreCrossingIdeal318

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open OriginalUpperActualFibreComponents318 (C fibreGeneric ambientGeneric ambientSupport ambientIdeal image_in_closure
  pointAt pointAt_reads idealAt_from_affine)
open OriginalUpperActualFibreIncidence318 (common ambient_generic_not_other generic_height_one)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Z : Scheme.{u}} [IsIntegral X] (s : X ⟶ Z) (p : Z)
variable (E F : C s p)
variable (x : X) (hx : x ∈ common s p E F)
local notation "A" => X.presheaf.stalk x
local notation "m" => IsLocalRing.maximalIdeal A
local notation "P₁" => PrimeSpectrum.asIdeal (pointAt s p E x (And.left hx))
local notation "P₂" => PrimeSpectrum.asIdeal (pointAt s p F x (And.right hx))

/-- The true scheme-theoretic crossing ideal after passage to the
ordinary ambient stalk. These are actual named point ideals, not two
chosen branches of an independent complete local ring. -/
abbrev cross : Ideal A := P₁ ⊔ P₂

theorem from_affine (U : X.affineOpens) (hxU : x ∈ U.1) :
    (((ambientIdeal s p E).ideal U) ⊔ ((ambientIdeal s p F).ideal U)).map
      (X.presheaf.germ U.1 x hxU).hom =
    cross s p E F x hx := by
  rw [Ideal.map_sup,idealAt_from_affine s p E U x hxU hx.1,
    idealAt_from_affine s p F U x hxU hx.2]

theorem proper : cross s p E F x hx ≠ ⊤ := by
  have h : cross s p E F x hx ≤ m :=
    sup_le (IsLocalRing.le_maximalIdeal_of_isPrime P₁)
      (IsLocalRing.le_maximalIdeal_of_isPrime P₂)
  exact (lt_of_le_of_lt h (IsLocalRing.maximalIdeal.isMaximal A).lt_top).ne

variable (different : E ≠ F) (closed : IsClosed ({p} : Set Z))
variable (vertical : s (genericPoint X) ≠ p) (dim : ∀ y : X, coheight y ≤ 2)

include different closed in
theorem ideals_ne : P₁ ≠ P₂ := by
  intro h
  have he : pointAt s p E x hx.1 = pointAt s p F x hx.2 := PrimeSpectrum.ext h
  have hEF := congrArg (fun t : Spec A => X.fromSpecStalk x t) he
  rw [pointAt_reads,pointAt_reads] at hEF
  have hF : ambientGeneric s p F ∈ ambientSupport s p F :=
    image_in_closure s p F ⟨fibreGeneric s p F,
      (genericPoints.isGenericPoint_ofComponent F).mem,rfl⟩
  exact ambient_generic_not_other s p E F different closed (hEF.symm ▸ hF)

include different closed vertical dim in
/-- Any prime of the actual crossing quotient comes from the true
closed stalk's maximal ideal. The calculation applies nonsplit and
uses only the true dimension-two regular model, not a completed split
nodal map. -/
theorem containing_prime (Q : Ideal A) (hQ : Q.IsPrime)
    (leQ : cross s p E F x hx ≤ Q) : Q = m := by
  let := hQ
  let H₁ := OriginalUpperGenerizationField318.codimension x (pointAt s p E x hx.1)
  let H₂ := OriginalUpperGenerizationField318.codimension x (pointAt s p F x hx.2)
  have h₁ : Ideal.height P₁ = 1 := by
    apply H₁.symm.trans
    change coheight (X.fromSpecStalk x (pointAt s p E x hx.1)) = 1
    rw [pointAt_reads]
    exact generic_height_one s p E F different closed vertical dim x hx
  have h₂ : Ideal.height P₂ = 1 := by
    apply H₂.symm.trans
    change coheight (X.fromSpecStalk x (pointAt s p F x hx.2)) = 1
    rw [pointAt_reads]
    exact generic_height_one s p F E different.symm closed vertical dim x ⟨hx.2,hx.1⟩
  have hmax : Ideal.height m ≤ 2 := by
    have H := OriginalUpperGenerizationField318.codimension x (IsLocalRing.closedPoint A)
    change coheight (X.fromSpecStalk x (IsLocalRing.closedPoint A)) = Ideal.height m at H
    rw [Scheme.fromSpecStalk_closedPoint] at H
    exact H ▸ dim x
  have hle₁ : P₁ ≤ Q := le_sup_left.trans leQ
  have hle₂ : P₂ ≤ Q := le_sup_right.trans leQ
  have oneLess : P₁ < Q := by
    refine lt_of_le_of_ne hle₁ ?_
    intro eq
    have qlt : P₂ < P₁ := lt_of_le_of_ne (eq.symm ▸ hle₂)
      (ideals_ne s p E F x hx different closed).symm
    have impossible := Ideal.height_add_one_le_of_lt_of_isPrime qlt
    rw [h₁,h₂] at impossible
    exact (by decide : ¬ (1 : ℕ∞) + 1 ≤ 1) impossible
  by_contra ne
  have qlt : Q < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime Q) ne
  have lower := Ideal.height_add_one_le_of_lt_of_isPrime oneLess
  rw [h₁] at lower
  have impossible := ((add_le_add_right lower (1 : ℕ∞)).trans
    (Ideal.height_add_one_le_of_lt_of_isPrime qlt)).trans hmax
  exact (by decide : ¬ (((1 : ℕ∞) + 1) + 1) ≤ 2) impossible

include different closed vertical dim in
theorem cross_radical : (cross s p E F x hx).radical = m := by
  apply le_antisymm
  · have h : cross s p E F x hx ≤ m :=
      sup_le (IsLocalRing.le_maximalIdeal_of_isPrime P₁)
        (IsLocalRing.le_maximalIdeal_of_isPrime P₂)
    exact (Ideal.radical_mono h).trans_eq (IsLocalRing.maximalIdeal.isMaximal A).isPrime.radical
  · rw [Ideal.radical_eq_sInf]
    exact le_sInf (fun Q hQ => (containing_prime s p E F x hx different closed vertical dim
      Q hQ.2 hQ.1).ge)

include different closed vertical dim in
theorem cross_dim_zero : Ring.KrullDimLE 0 (A ⧸ cross s p E F x hx) :=
  Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun Q hQ =>
    (containing_prime s p E F x hx different closed vertical dim Q hQ.1.1 hQ.1.2).symm ▸
      IsLocalRing.maximalIdeal.isMaximal A

/-- The true local intersection module, before inserting the residue
degree, is the ordinary quotient by the two genuine component ideals. -/
abbrev length : ℕ∞ := Module.length A (A ⧸ cross s p E F x hx)

theorem length_positive : 0 < length s p E F x hx :=
  Module.length_pos_iff.mpr (Ideal.Quotient.nontrivial_iff.mpr (proper s p E F x hx))

/-- At a true thin semistable crossing with two distinguished
original components, the chart equation identifies the sum with the
maximal ideal. Under that actual ideal equality the length is one,
without any additional Artinian stock. -/
omit [IsIntegral X] in
theorem thin_length_one (node : cross s p E F x hx = m) :
    length s p E F x hx = 1 := by
  change Module.length A (A ⧸ cross s p E F x hx) = 1
  rw [node]
  apply Module.length_eq_one_iff.mpr
  exact isSimpleModule_iff_quot_maximal.mpr
    ⟨m,IsLocalRing.maximalIdeal.isMaximal A,⟨LinearEquiv.refl _ _⟩⟩

end OriginalUpperActualFibreCrossingIdeal318

#print axioms OriginalUpperActualFibreCrossingIdeal318.from_affine
#print axioms OriginalUpperActualFibreCrossingIdeal318.cross_radical
#print axioms OriginalUpperActualFibreCrossingIdeal318.cross_dim_zero
#print axioms OriginalUpperActualFibreCrossingIdeal318.thin_length_one
