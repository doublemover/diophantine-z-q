module
public import CTOriginalActualShaDefinition318
public import CTOriginalFullBoundaryHom318
public import Mathlib.GroupTheory.QuotientGroup.Basic
import all CTOriginalActualShaDefinition318
import all CTOriginalFullEllipticHOneKernel318
import all CTOriginalContinuousEllipticCocycles318
import all CTOriginalFullCocycleRestriction318
import all CTOriginalFullBoundaryHom318
public section
noncomputable section

namespace ActualContinuousShaKernel318

open groupCohomology
open ActualTwoDescentActualShaDefinition318 ActualTwoDescentEllipticModel318
open ActualTwoDescentContinuousEllipticCocycles318 ActualTwoDescentFullEllipticHOneKernel318
open ActualTwoDescentFullBoundaryHom318 ActualTwoDescentFullEllipticRepresentation318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentGeometricPointTransport318
open ActualTwoDescentSquareClassFieldMap318

variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Literal continuous degree-one cohomology: discrete geometric
points, locally constant cocycles modulo actual boundaries. -/
abbrev ContH1 (n : F) (hn : n≠0) :=
  continuousFullCocycles n hn ⧸ (fullBoundaryHom n hn).range

abbrev contClass (n : F) (hn : n≠0) : continuousFullCocycles n hn →+ ContH1 n hn :=
  QuotientAddGroup.mk' (fullBoundaryHom n hn).range

theorem class_kernel_exact (n : F) (hn : n≠0) :
    (fullClassHom n hn).ker=(fullBoundaryHom n hn).range := by
  ext z
  change fullClassHom n hn z=0 ↔ ∃ Q, fullBoundaryHom n hn Q=z
  constructor
  · intro hz
    obtain ⟨Q,hQ⟩ := (actual_full_class_zero n hn z).mp hz
    exact ⟨Q,by apply Subtype.ext; apply Subtype.ext; exact (funext hQ).symm⟩
  · rintro ⟨Q,rfl⟩
    exact actual_full_boundary_zero n hn Q

def contToNative (n : F) (hn : n≠0) : ContH1 n hn →+ H1 (fullEllipticRep n hn) :=
  QuotientAddGroup.lift _ (fullClassHom n hn) (class_kernel_exact n hn).ge

@[simp] theorem cont_to_native_mk (n : F) (hn : n≠0) (z : continuousFullCocycles n hn) :
    contToNative n hn (contClass n hn z)=fullClassHom n hn z :=
  QuotientAddGroup.lift_mk' _ _ z

theorem cont_to_native_injective (n : F) (hn : n≠0) : Function.Injective (contToNative n hn) := by
  intro x y he
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b,rfl⟩ := QuotientAddGroup.mk_surjective y
  have hEq : fullClassHom n hn a=fullClassHom n hn b := by
    simpa only [cont_to_native_mk] using he
  have hm : a-b∈(fullClassHom n hn).ker := by
    change fullClassHom n hn (a-b)=0
    rw [map_sub,hEq,sub_self]
  rw [class_kernel_exact n hn] at hm
  have hz : contClass n hn (a-b)=0 := (QuotientAddGroup.eq_zero_iff (a-b)).mpr hm
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

theorem cont_to_native_range (n : F) (hn : n≠0) :
    (contToNative n hn).range=continuousFullHOne n hn := by
  ext x
  change (∃ y : ContH1 n hn, contToNative n hn y=x) ↔
    ∃ z : continuousFullCocycles n hn, fullClassHom n hn z=x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨z,by simpa only [cont_to_native_mk] using hy⟩
  · rintro ⟨z,hz⟩
    exact ⟨contClass n hn z,(cont_to_native_mk n hn z).trans hz⟩

/-- Boundary-compatible restriction on the actual continuous
quotient. Both the map on the groups and the map on points are
the existing chosen absolute Galois restriction and closureMap. -/
def contRestrict (f : F →+* L) (n : F) (hn : n≠0) :
    ContH1 n hn →+ ContH1 (f n) (field_map_ne_zero f hn) :=
  QuotientAddGroup.lift _
    ((contClass (f n) (field_map_ne_zero f hn)).comp (fullCocycleRestriction f n hn))
    (by
      rintro z ⟨Q,rfl⟩
      change contClass (f n) (field_map_ne_zero f hn)
        (fullCocycleRestriction f n hn (fullBoundary n hn Q))=0
      rw [actual_full_restriction_boundary]
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨closurePointMap f n hn Q,rfl⟩)

@[simp] theorem cont_restrict_mk (f : F →+* L) (n : F) (hn : n≠0) (z : continuousFullCocycles n hn) :
    contRestrict f n hn (contClass n hn z)=
      contClass (f n) (field_map_ne_zero f hn) (fullCocycleRestriction f n hn z) :=
  QuotientAddGroup.lift_mk' _ _ z

theorem restrict_mk_zero_iff (f : F →+* L) (n : F) (hn : n≠0) (z : continuousFullCocycles n hn) :
    contRestrict f n hn (contClass n hn z)=0 ↔
      fullClassHom (f n) (field_map_ne_zero f hn) (fullCocycleRestriction f n hn z)=0 := by
  rw [cont_restrict_mk]
  constructor
  · intro h
    simpa only [cont_to_native_mk,map_zero] using
      congrArg (contToNative (f n) (field_map_ne_zero f hn)) h
  · intro h
    apply cont_to_native_injective
    simpa only [cont_to_native_mk,map_zero] using h

/-- Classical continuous Sha as the kernel of all actual local
maps. The real component is retained, even though the result
below only uses a dyadic subgroup. -/
def continuousSha (n : ℚ) (hn : n≠0) : AddSubgroup (ContH1 n hn) where
  carrier := {x | contRestrict (algebraMap ℚ ℝ) n hn x=0 ∧
    ∀ (p : ℕ) [Fact p.Prime], contRestrict (algebraMap ℚ (ℚ_[p])) n hn x=0}
  zero_mem' := ⟨map_zero _,fun _ _ => map_zero _⟩
  add_mem' := by
    rintro a b ⟨ha,hpa⟩ ⟨hb,hpb⟩
    exact ⟨by rw [map_add,ha,hb,zero_add],fun p _ => by rw [map_add,hpa p,hpb p,zero_add]⟩
  neg_mem' := by
    rintro a ⟨ha,hpa⟩
    exact ⟨by rw [map_neg,ha,neg_zero],fun p _ => by rw [map_neg,hpa p,neg_zero]⟩

theorem mem_cont_sha_mk_iff (n : ℚ) (hn : n≠0) (z : continuousFullCocycles n hn) :
    contClass n hn z∈continuousSha n hn ↔ EverywhereLocallyTrivial n hn z := by
  change ((contRestrict (algebraMap ℚ ℝ) n hn (contClass n hn z)=0) ∧
    ∀ (p : ℕ) [Fact p.Prime], contRestrict (algebraMap ℚ (ℚ_[p])) n hn (contClass n hn z)=0) ↔ _
  simp only [restrict_mk_zero_iff,EverywhereLocallyTrivial]

def shaToNative (n : ℚ) (hn : n≠0) : continuousSha n hn →+ actualSha n hn where
  toFun x := ⟨contToNative n hn (x : ContH1 n hn),by
    obtain ⟨z,hz⟩ := QuotientAddGroup.mk_surjective (x : ContH1 n hn)
    have h : contClass n hn z∈continuousSha n hn := by
      change QuotientAddGroup.mk z∈continuousSha n hn
      rw [hz]
      exact x.property
    exact ⟨z,by rw [← hz,cont_to_native_mk],(mem_cont_sha_mk_iff n hn z).mp h⟩⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _

/-- The formal comparison required to apply the classical Sha
statement to the actual native all-local kernel. No arithmetic
duality or merely ordinary-cohomology surjectivity is assumed. -/
def shaEquivNative (n : ℚ) (hn : n≠0) : continuousSha n hn ≃+ actualSha n hn :=
  AddEquiv.ofBijective (shaToNative n hn) ⟨by
    intro a b h
    apply Subtype.ext
    apply cont_to_native_injective n hn
    exact congrArg Subtype.val h,by
    intro x
    obtain ⟨z,hz,hL⟩ := x.property
    refine ⟨⟨contClass n hn z,(mem_cont_sha_mk_iff n hn z).mpr hL⟩,?_⟩
    apply Subtype.ext
    change contToNative n hn (contClass n hn z)=x.val
    rw [cont_to_native_mk,hz]⟩

theorem sha_equiv_dyadic (n : ℚ) (hn : n≠0) (k : ℕ) (x : continuousSha n hn) :
    (2^k:ℕ) • shaEquivNative n hn x=0 ↔ (2^k:ℕ) • x=0 := by
  rw [← map_nsmul]
  constructor
  · intro h
    exact (shaEquivNative n hn).injective (h.trans (map_zero _).symm)
  · intro h
    rw [h,map_zero]

end ActualContinuousShaKernel318
