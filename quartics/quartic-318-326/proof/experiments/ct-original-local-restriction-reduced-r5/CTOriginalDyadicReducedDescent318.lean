module
public import CTOriginalContinuousShaKernel318
public import CTOriginalActualShaPrimary318
public import CTOriginalActualShaReducedDuality318
public import CTPrimaryPowerRoots318
public import FiniteInvolutionPrimaryCore318
public import Mathlib.Algebra.Group.Subgroup.Map
import all CTPrimaryPowerRoots318
import all CTOriginalActualShaReducedDuality318
import all CTOriginalActualShaReducedPrimary318
import all CTOriginalReducedPrimaryQuotient318
public section
noncomputable section

namespace ActualPrimaryCTKernelAdapter318

open ActualContinuousShaKernel318 PrimaryDivisibleIntersection318
open ActualTwoDescentActualShaPrimary318 ActualTwoDescentStablePrimaryCore318
open ActualTwoDescentActualShaReducedPrimary318 ActualTwoDescentActualShaReducedDuality318

abbrev CTValues := Multiplicative (AddCircle (1:ℚ))

/-- Precisely the p=2 arithmetic input: an alternating form on the
whole continuous 2-primary Sha with its maximal divisible left
radical. Neither odd torsion nor full Sha finiteness is a premise. -/
@[expose] def PrimaryRadicalPairing (A : Type*) [CommGroup A] : Prop :=
  ∃ B : A →* (A →* CTValues),
    (∀ x, B x x=1) ∧ HasPowerRoots B.ker ∧
    ∀ D : Subgroup A, HasPowerRoots D → D≤B.ker

abbrev ContinuousPrimary (n : ℚ) (hn : n≠0) :=
  CommGroup.primaryComponent (Multiplicative (continuousSha n hn)) 2

private def primaryImage {A B : Type*} [CommGroup A] [CommGroup B] (e : A →* B) :
    CommGroup.primaryComponent A 2 →* CommGroup.primaryComponent B 2 where
  toFun x := ⟨e (x:A),by
    obtain ⟨k,hk⟩ := CommGroup.mem_primaryComponent.mp x.property
    exact CommGroup.mem_primaryComponent.mpr ⟨k,by rw [← map_pow,hk,map_one]⟩⟩
  map_one' := Subtype.ext (map_one e)
  map_mul' x y := Subtype.ext (map_mul e (x:A) (y:A))

def primaryEquivNative (n : ℚ) (hn : n≠0) :
    ContinuousPrimary n hn ≃* actualShaPrimary n hn := by
  let e := (shaEquivNative n hn).toMultiplicative
  refine
    { toFun := primaryImage e.toMonoidHom
      invFun := primaryImage e.symm.toMonoidHom
      left_inv := fun x => Subtype.ext (e.symm_apply_apply (x:_))
      right_inv := fun x => Subtype.ext (e.apply_symm_apply (x:_))
      map_mul' := map_mul (primaryImage e.toMonoidHom) }

private theorem has_roots_comap {A B : Type*} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (D : Subgroup B) (hD : HasPowerRoots D) :
    HasPowerRoots (D.comap e.toMonoidHom) := by
  intro m hm x
  obtain ⟨y,hy⟩ := hD m hm ⟨e (x:A),x.property⟩
  refine ⟨⟨e.symm (y:B),?_⟩,?_⟩
  · change e (e.symm (y:B))∈D
    simpa only [MulEquiv.apply_symm_apply] using y.property
  · apply Subtype.ext
    apply e.injective
    change e ((e.symm (y:B))^m)=e (x:A)
    rw [map_pow,MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val hy

private theorem radical_pullback {A B : Type*} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (h : PrimaryRadicalPairing B) : PrimaryRadicalPairing A := by
  obtain ⟨P,hAlt,hD,hMax⟩ := h
  let Q : A →* A →* CTValues :=
    { toFun := fun x => (P (e x)).comp e.toMonoidHom
      map_one' := by
        apply MonoidHom.ext
        intro y
        change P (e 1) (e y)=1
        simp
      map_mul' x y := by
        apply MonoidHom.ext
        intro z
        change P (e (x*y)) (e z)=P (e x) (e z)*P (e y) (e z)
        simp }
  have hk : Q.ker=P.ker.comap e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      change Q x=1 at hx
      change P (e x)=1
      apply MonoidHom.ext
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      change Q x z=1
      simpa only [MonoidHom.one_apply] using congrArg (fun q : A →* CTValues => q z) hx
    · intro hx
      change P (e x)=1 at hx
      change Q x=1
      apply MonoidHom.ext
      intro y
      change P (e x) (e y)=1
      simpa only [MonoidHom.one_apply] using congrArg (fun p : B →* CTValues => p (e y)) hx
  refine ⟨Q,fun x => hAlt (e x),by rw [hk]; exact has_roots_comap e _ hD,?_⟩
  intro D hD'
  rw [hk]
  apply Subgroup.map_le_iff_le_comap.mp
  apply hMax
  rw [Subgroup.map_equiv_eq_comap_symm]
  exact has_roots_comap e.symm D hD'

private theorem quotient_pairing_of_exact_radical {A V : Type*} [CommGroup A] [CommGroup V]
    (C : Subgroup A) (B : A →* A →* V) (hAlt : ∀ x, B x x=1) (hKer : B.ker=C) :
    ∃ e : (A ⧸ C) →* ((A ⧸ C) →* V),
      (∀ x, e x x=1) ∧ (∀ x, (∀ y, e x y=1) → x=1) := by
  have hSwap (x y : A) : B x y * B y x=1 := by
    simpa only [map_mul,MonoidHom.mul_apply,hAlt,one_mul,mul_one] using hAlt (x*y)
  have hleft {x : A} (hx : x∈C) (y : A) : B x y=1 := by
    have hk : x∈B.ker := hKer.symm ▸ hx
    change B x=1 at hk
    simpa only [MonoidHom.one_apply] using congrArg (fun q : A →* V => q y) hk
  have hright (x : A) {y : A} (hy : y∈C) : B x y=1 := by
    have h := hSwap x y
    rwa [hleft hy x,mul_one] at h
  let row (x : A) : (A ⧸ C) →* V :=
    QuotientGroup.lift C (B x) (fun y hy => hright x hy)
  have hrow (x y : A) : row x (QuotientGroup.mk y)=B x y :=
    QuotientGroup.lift_mk' C _ y
  let rows : A →* ((A ⧸ C) →* V) :=
    { toFun := row
      map_one' := by
        apply MonoidHom.ext
        intro y
        obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective y
        change row 1 (QuotientGroup.mk z)=1
        simp only [hrow,map_one,MonoidHom.one_apply]
      map_mul' x y := by
        apply MonoidHom.ext
        intro q
        obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective q
        change row (x*y) (QuotientGroup.mk z)=row x (QuotientGroup.mk z)*row y (QuotientGroup.mk z)
        simp only [hrow,map_mul,MonoidHom.mul_apply] }
  have hrows : C≤rows.ker := by
    intro x hx
    change row x=1
    apply MonoidHom.ext
    intro q
    obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective q
    change row x (QuotientGroup.mk z)=1
    rw [hrow]
    exact hleft hx z
  let e := QuotientGroup.lift C rows hrows
  have he (x y : A) :
      e (QuotientGroup.mk x) (QuotientGroup.mk y)=B x y := by
    change QuotientGroup.lift C rows hrows (QuotientGroup.mk x) (QuotientGroup.mk y)=_
    rw [QuotientGroup.lift_mk']
    exact hrow x y
  refine ⟨e,?_,?_⟩
  · intro x
    obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective x
    rw [he]
    exact hAlt u
  · intro x hx
    obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective x
    apply (QuotientGroup.eq_one_iff u).mpr
    rw [← hKer]
    change B u=1
    apply MonoidHom.ext
    intro y
    exact (he u y).symm.trans (hx (QuotientGroup.mk y))

/-- The general nonzero original rational model: full continuous dyadic Sha
with its exact alternating arithmetic pairing and radical, plus finiteness of
the actual two-torsion only, suffice for the native reduced duality pairing.
There is no finite full Sha, selected Selmer cardinality, or rank hypothesis. -/
theorem reduced_of_primary_of_finite_involutions (n : ℚ) (hn : n≠0)
    (hFin : Finite ((powMonoidHom (α:=actualShaPrimary n hn) 2).ker))
    (hCT : PrimaryRadicalPairing (ContinuousPrimary n hn)) : ActualReducedDuality n hn := by
  have hC : HasPowerRoots (actualShaDivisibleCore n hn) ∧
      ∀ D : Subgroup (actualShaPrimary n hn), HasPowerRoots D → D≤actualShaDivisibleCore n hn :=
    FiniteInvolutionPrimaryCore318.maximal_divisible_of_finite_involutions
      (actual_sha_primary_is_two_group n hn) hFin (actualShaDivisibleCore n hn)
      (actual_stable_core_mem (actualShaPrimary n hn))
  obtain ⟨B,hAlt,hRoots,hMax⟩ := radical_pullback (primaryEquivNative n hn).symm hCT
  have hKer : B.ker=actualShaDivisibleCore n hn :=
    le_antisymm (hC.2 _ hRoots) (hMax _ hC.1)
  exact quotient_pairing_of_exact_radical _ B hAlt hKer

end ActualPrimaryCTKernelAdapter318
