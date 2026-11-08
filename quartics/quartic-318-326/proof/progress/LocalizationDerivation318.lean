module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.Basic
public section
noncomputable section
namespace LocalizationDerivation318
set_option maxHeartbeats 500000
universe u
variable {R : Type*} {S : Type*} {T : Type*} {M : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [AddCommGroup M] [Module S M] [Module T M] [Module R M]
  [IsScalarTower S T M] [IsScalarTower R S M] [IsScalarTower R T M]
  (P : Submonoid S) [IsLocalization P T]

local instance oppositeModule : Module Tᵐᵒᵖ M :=
  Module.compHom M (RingEquiv.toOpposite T).symm.toRingHom
local instance centralModule : IsCentralScalar T M where
  op_smul_eq_smul _ _ := rfl
local instance oppositeTower : IsScalarTower R Tᵐᵒᵖ M where
  smul_assoc r t m := by
    change (r • t.unop) • m = r • (t.unop • m)
    exact smul_assoc r t.unop m

/-- The square-zero jet of a derivation into an arbitrary module over the
localized ring. No domain, field, or rank-one assumption is used. -/
@[expose] def jet (d : Derivation R S M) : S →ₐ[R] TrivSqZeroExt T M where
  toFun s := TrivSqZeroExt.inl (algebraMap S T s) + TrivSqZeroExt.inr (d s)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp [d.map_one_eq_zero]
  map_add' s t := by apply TrivSqZeroExt.ext <;> simp
  map_mul' s t := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [d.leibniz, IsScalarTower.algebraMap_smul T]
  commutes' r := by
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl', IsScalarTower.algebraMap_apply R S T]
    · simp [TrivSqZeroExt.algebraMap_eq_inl', d.map_algebraMap]

theorem jet_unit (d : Derivation R S M) (s : P) : IsUnit (jet (T:=T) d s) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  simpa [jet] using IsLocalization.map_units T s

@[expose] def extendedJet (d : Derivation R S M) : T →ₐ[R] TrivSqZeroExt T M :=
  IsLocalization.liftAlgHom (M:=P) (jet_unit P d)

theorem extendedJet_algebraMap (d : Derivation R S M) (s : S) :
    extendedJet P d (algebraMap S T s) = jet d s :=
  IsLocalization.lift_eq (jet_unit P d) s

theorem extendedJet_fst (d : Derivation R S M) (t : T) :
    (extendedJet P d t).fst = t := by
  have h : (TrivSqZeroExt.fstHom R T M).comp (extendedJet P d) = AlgHom.id R T := by
    apply IsLocalization.algHom_ext P
    ext s
    change (extendedJet P d (algebraMap S T s)).fst = algebraMap S T s
    rw [extendedJet_algebraMap]
    simp [jet]
  exact congrArg (fun f : T →ₐ[R] T => f t) h

/-- A genuine unique extension of an arbitrary relative derivation to a
localization, with values in any module over that localization. -/
@[expose] def extend (d : Derivation R S M) : Derivation R T M where
  toLinearMap := ((TrivSqZeroExt.sndHom T M).restrictScalars R).comp (extendedJet P d).toLinearMap
  map_one_eq_zero' := by
    change (extendedJet P d 1).snd = 0
    rw [map_one,TrivSqZeroExt.snd_one]
  leibniz' s t := by
    change (extendedJet P d (s*t)).snd = s • (extendedJet P d t).snd + t • (extendedJet P d s).snd
    rw [map_mul,TrivSqZeroExt.snd_mul,extendedJet_fst,extendedJet_fst]
    simp [add_comm]

theorem extend_algebraMap (d : Derivation R S M) (s : S) :
    extend P d (algebraMap S T s) = d s := by
  change (extendedJet P d (algebraMap S T s)).snd = d s
  rw [extendedJet_algebraMap]
  simp [jet]

/-- The localization uniqueness argument uses only the additive Leibniz rule. -/
theorem additive_ext (P : Submonoid S) [IsLocalization P T] (d e : T →+ M)
    (hd : ∀ a b, d (a*b)=a • d b + b • d a)
    (he : ∀ a b, e (a*b)=a • e b + b • e a)
    (h : ∀ s : S, d (algebraMap S T s)=e (algebraMap S T s)) : d=e := by
  ext t
  obtain ⟨⟨a,s⟩,ht⟩ := IsLocalization.surj P t
  apply (IsLocalization.map_units T s).smul_left_cancel.mp
  have hh := congrArg d ht
  have hh' := congrArg e ht
  rw [hd,h a,h s] at hh
  rw [he] at hh'
  exact add_left_cancel (hh.trans hh'.symm)

theorem derivation_ext (P : Submonoid S) [IsLocalization P T] (d e : Derivation R T M)
    (h : ∀ s : S, d (algebraMap S T s)=e (algebraMap S T s)) : d=e := by
  have hh := additive_ext P d.toLinearMap.toAddMonoidHom e.toLinearMap.toAddMonoidHom
    d.leibniz e.leibniz h
  ext t
  exact congrArg (fun f : T →+ M => f t) hh

theorem unique (d : Derivation R S M) (D : Derivation R T M)
    (h : ∀ s : S, D (algebraMap S T s)=d s) : D=extend P d := by
  apply derivation_ext P
  intro s
  rw [h,extend_algebraMap]
end LocalizationDerivation318
