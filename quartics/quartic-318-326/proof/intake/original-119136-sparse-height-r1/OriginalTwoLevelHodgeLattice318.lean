module
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic
public section
noncomputable section

/-! Build the global original Hodge coefficient IDEAL from the two genuine
open Hodge lattices on the same generic line. No global ideal, global
basis, or standalone finite-place metric is a descent input. -/
namespace OriginalTwoLevelHodgeLattice318
open scoped nonZeroDivisors
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Exact membership on a principal open, measured in the same generic space. -/
def sat (n : R) (P : Submodule R V) : Submodule R V where
  carrier := {x | ∃k : ℕ,n^k • x∈P}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro x y ⟨k,hk⟩ ⟨l,hl⟩
    refine ⟨k+l,?_⟩
    rw [smul_add]
    apply P.add_mem
    · rw [Nat.add_comm,pow_add,mul_smul]; exact P.smul_mem _ hk
    · rw [pow_add,mul_smul]; exact P.smul_mem _ hl
  smul_mem' := by
    rintro r x ⟨k,hk⟩
    exact ⟨k,(smul_comm (n^k) r x).symm ▸ P.smul_mem r hk⟩

theorem le_sat (n : R) (P : Submodule R V) : P≤sat n P :=
  fun x hx => ⟨0,by simpa using hx⟩

theorem sat_mono (n : R) {P Q : Submodule R V} (le : P≤Q) : sat n P≤sat n Q :=
  fun _ ⟨k,hk⟩ => ⟨k,le hk⟩

theorem double_sat (r s : R) (P : Submodule R V) :
    sat s (sat r P)=sat (r*s) P := by
  apply le_antisymm
  · rintro x ⟨k,l,hl⟩
    refine ⟨k+l,?_⟩
    have he : (r*s)^(k+l)=(r^k*s^l)*(r^l*s^k) := by rw [mul_pow,pow_add,pow_add]; ring
    rw [he,mul_smul (r^k*s^l) (r^l*s^k),mul_smul (r^l) (s^k)]
    exact P.smul_mem _ hl
  · rintro x ⟨k,hk⟩
    exact ⟨k,k,by simpa only [mul_pow,mul_smul] using hk⟩

theorem idem (n : R) (P : Submodule R V) : sat n (sat n P)=sat n P := by
  apply le_antisymm _ (le_sat _ _)
  rintro x ⟨k,l,hl⟩
  exact ⟨l+k,by simpa only [pow_add,mul_smul] using hl⟩

theorem coprime_inter (r s : R) (cop : IsCoprime r s) (W : Submodule R V) :
    sat r W ⊓ sat s W=W := by
  apply le_antisymm _ (le_inf (le_sat _ _) (le_sat _ _))
  rintro x ⟨⟨k,hk⟩,⟨l,hl⟩⟩
  obtain ⟨a,b,eq⟩ := cop.pow (m:=k) (n:=l)
  have he : x=a • (r^k • x)+b • (s^l • x) := by
    rw [←mul_smul,←mul_smul,←add_smul,eq,one_smul]
  rw [he]
  exact W.add_mem (W.smul_mem _ hk) (W.smul_mem _ hl)

/-- A section in P has some r-power multiple in Q because it already lands
in their COMMON overlap. Inf is in the same generic ambient module. -/
theorem recover (r s : R) (P Q : Submodule R V) (stable : sat r P=P)
    (agree : sat s P=sat r Q) : sat r (P⊓Q)=P := by
  apply le_antisymm ((sat_mono r inf_le_left).trans_eq stable)
  intro x hx
  have h : x∈sat r Q := agree ▸ le_sat s P hx
  obtain ⟨k,hk⟩ := h
  exact ⟨k,P.smul_mem _ hx,hk⟩

section Open
variable {E : Type*} [Field E] [Algebra R E]

/-- The saturation really is restriction to an actual standard affine ring. -/
theorem on_open (S : Type*) [CommRing S] [Algebra R S] [Algebra S E] [IsScalarTower R S E]
    (n : R) [IsLocalization.Away n S] (g : Set E) :
    sat n (Submodule.span R g)=(Submodule.span S g).restrictScalars R := by
  let W := Submodule.span R g
  let L := Submodule.span S g
  apply le_antisymm
  · rintro x ⟨k,hk⟩
    have h' := Submodule.span_le_restrictScalars R S g hk
    obtain ⟨u,hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S:=S) n).pow k
    have ux : (u:S) • x∈L := by
      rw [hu,←map_pow,IsScalarTower.algebraMap_smul]
      exact h'
    have z := L.smul_mem (↑(u⁻¹):S) ux
    change x∈L
    simpa only [←mul_smul,Units.inv_mul,one_smul] using z
  · intro x hx
    change x∈L at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact le_sat n W (Submodule.subset_span hx)
    | zero => exact (sat n W).zero_mem
    | add a b ha hb ia ib => exact (sat n W).add_mem ia ib
    | smul s x hx ih =>
      obtain ⟨k,hk⟩ := ih
      obtain ⟨l,a,ha⟩ := IsLocalization.Away.surj n s
      have hs := congrArg (algebraMap S E) ha
      simp only [map_mul,map_pow,←IsScalarTower.algebraMap_apply] at hs
      have he : n^(k+l) • (s • x)=a • (n^k • x) := by
        simp only [Algebra.smul_def,pow_add,map_mul,map_pow]
        calc _=(algebraMap S E s*(algebraMap R E n)^l)*((algebraMap R E n)^k*x) := by ring
             _=_ := by rw [hs]
      exact ⟨k+l,he.symm ▸ W.smul_mem a hk⟩
end Open

variable {E : Type*} [Field E] [Algebra R E]

theorem sat_bot (r : R) (nr : algebraMap R E r≠0) : sat r (⊥ : Submodule R E)=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨k,hk⟩
  change r^k • x=0 at hk
  rw [Algebra.smul_def,map_pow] at hk
  exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero _ nr)

variable [IsFractionRing R E]

/-- A finitely generated *upper bound* for the intersection suffices.
There is no requirement that generators already agree or be integral on
both opens. Thus global finite generation need not be inserted as a
third compatibility hypothesis. -/
theorem glue (r s : R) (cop : IsCoprime r s) (G J : Finset E)
    (agree : sat (r*s) (Submodule.span R (G:Set E))=sat (r*s) (Submodule.span R (J:Set E))) :
    ∃ I : FractionalIdeal R⁰ E,
      (I:Submodule R E)=sat r (Submodule.span R (G:Set E)) ⊓ sat s (Submodule.span R (J:Set E)) ∧
      sat r (I:Submodule R E)=sat r (Submodule.span R (G:Set E)) ∧
      sat s (I:Submodule R E)=sat s (Submodule.span R (J:Set E)) := by
  classical
  let P := sat r (Submodule.span R (G:Set E))
  let Q := sat s (Submodule.span R (J:Set E))
  let W := Submodule.span R ((G∪J:Finset E):Set E)
  have fg : W.FG := ⟨G∪J,rfl⟩
  let U : FractionalIdeal R⁰ E := ⟨W,FractionalIdeal.isFractional_of_fg fg⟩
  have pW : P≤sat r W := sat_mono _ (Submodule.span_mono (by
    intro x hx; exact Finset.mem_union.mpr (Or.inl hx)))
  have qW : Q≤sat s W := sat_mono _ (Submodule.span_mono (by
    intro x hx; exact Finset.mem_union.mpr (Or.inr hx)))
  have upper : P⊓Q≤W := (inf_le_inf pW qW).trans_eq (coprime_inter r s cop W)
  let I : FractionalIdeal R⁰ E := ⟨P⊓Q,FractionalIdeal.isFractional_of_le (J:=U) upper⟩
  have same : sat s P=sat r Q := by
    change sat s (sat r _)=sat r (sat s _)
    rw [double_sat,double_sat,mul_comm s r,agree]
  refine ⟨I,rfl,recover r s P Q (idem _ _) same,?_⟩
  change sat s (P⊓Q)=Q
  rw [inf_comm]
  exact recover s r Q P (idem _ _) same.symm

end OriginalTwoLevelHodgeLattice318
