module

public import IntrinsicDifferentialPullback318
public import PulledCoordinateMaps318
public import ModuleTopExt318
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# The two genuine sheaf maps of the actual directional fibre row

The epsilon differential is pulled from the literal deformation-base parameter.
The right map is the adjoint of the actual differential pullback. This file
constructs the complex; short exactness is a separate local assertion.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite

namespace SelectedSameAActualFibreSheafArrows318

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k]
variable {X A : Scheme.{u}}

abbrev D (k : Type u) := TrivSqZeroExt k k
abbrev spec (R : Type u) [CommRing R] : Scheme.{u} := Spec (CommRingCat.of R)
abbrev sMap {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T) :
    spec T ⟶ spec R := Spec.map (CommRingCat.ofHom f)
abbrev eps (k : Type u) [CommRing k] : D k := TrivSqZeroExt.inr 1
abbrev pr (k : Type u) [CommRing k] : D k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
abbrev inc (k : Type u) [CommRing k] : k →+* D k := TrivSqZeroExt.inlHom k k

variable (σ : X ⟶ spec (D k)) (ρ : A ⟶ X) (a : A ⟶ spec k)
variable (h : ρ ≫ σ = a ≫ sMap (pr k))

/-- The structure over k is the actual deformation structure followed
by the given inclusion of the constants in the dual numbers. -/
def xOverK : X ⟶ spec k := σ ≫ sMap (inc k)

include h in
theorem fibre_over_k : ρ ≫ xOverK σ = a := by
  have hk : CommRingCat.ofHom (inc k) ≫ CommRingCat.ofHom (pr k) =
      𝟙 (CommRingCat.of k) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    change (TrivSqZeroExt.inl t : D k).fst = t
    exact TrivSqZeroExt.fst_inl _ _
  unfold xOverK
  rw [← Category.assoc, h, Category.assoc, ← Spec.map_comp, hk, Spec.map_id, Category.comp_id]

/-- Pull the actual marked epsilon function from the deformation base. -/
noncomputable def epsilonSection : Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (D k))).inv ≫ σ.appTop) (eps k)

include h in
theorem epsilon_on_fibre_zero : ρ.appTop (epsilonSection σ) = 0 := by
  have h0 : ((Scheme.ΓSpecIso (CommRingCat.of (D k))).inv ≫ σ.appTop) ≫ ρ.appTop =
      (CommRingCat.ofHom (pr k) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv) ≫ a.appTop := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  have he := congrArg (fun f : CommRingCat.of (D k) ⟶ Γ(A, ⊤) => f (eps k)) h0
  change ρ.appTop (epsilonSection σ) = a.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv
    (pr k (eps k))) at he
  rw [he]
  have hp : pr k (eps k) = 0 := by
    change (TrivSqZeroExt.inr (R := k) (1 : k)).fst = 0
    exact TrivSqZeroExt.fst_inr (R := k) (1 : k)
  rw [hp, map_zero, map_zero]

abbrev omegaX := FamilyIntrinsicDifferentials318.omega (xOverK σ)
abbrev omegaA := FamilyIntrinsicDifferentials318.omega a
abbrev unit (Y : Scheme.{u}) : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

/-- The true pulled absolute differential sheaf, over the literal fibre. -/
abbrev middle : A.Modules := (Scheme.Modules.pullback ρ).obj (omegaX σ)

/-- The underlying global differential of the same epsilon before restriction. -/
noncomputable def rawLeft : unit X ⟶ omegaX σ :=
  ModuleGlobalSections318.ofTop _ ((FamilyIntrinsicDifferentials318.D (xOverK σ)).d
    (epsilonSection σ))

/-- The marked line inclusion on the fibre is the actual pullback
of the preceding global differential, including the unit comparison. -/
noncomputable def left : unit A ⟶ middle σ ρ :=
  PulledCoordinateMaps318.map ρ (rawLeft σ)

include h in
/-- The actual right arrow maps the pulled differential of any local
regular function to the differential of its real reduction. -/
noncomputable def right : middle σ ρ ⟶ omegaA a :=
  IntrinsicDifferentialPullback318.pullbackMap ρ a (xOverK σ) (fibre_over_k σ ρ a h)

include h in
private theorem raw_composite_zero :
    rawLeft σ ≫ IntrinsicDifferentialPullback318.map ρ a (xOverK σ) (fibre_over_k σ ρ a h) = 0 := by
  let q : omegaX σ ⟶ (Scheme.Modules.pushforward ρ).obj (omegaA a) :=
    IntrinsicDifferentialPullback318.map ρ a (xOverK σ) (fibre_over_k σ ρ a h)
  let w : Γ(omegaX σ, ⊤) := (FamilyIntrinsicDifferentials318.D (xOverK σ)).d
    (epsilonSection σ)
  have hv : q.app ⊤ w = (FamilyIntrinsicDifferentials318.D a).d
      (ρ.appTop (epsilonSection σ)) :=
    IntrinsicDifferentialPullback318.globalSection_D ρ a (xOverK σ)
      (fibre_over_k σ ρ a h) (epsilonSection σ)
  have hz : (FamilyIntrinsicDifferentials318.D a).d (X := op (⊤ : A.Opens)) 0 = 0 :=
    AddMonoidHom.map_zero ((FamilyIntrinsicDifferentials318.D a).d (X := op (⊤ : A.Opens)))
  have hv' : q.app ⊤ w = 0 :=
    hv.trans ((congrArg (FamilyIntrinsicDifferentials318.D a).d
      (epsilon_on_fibre_zero σ ρ a h)).trans hz)
  change ModuleGlobalSections318.ofTop (omegaX σ) w ≫ q = 0
  rw [ModuleTopMorphisms318.ofTop_comp, hv']
  let Z : X.Modules := (Scheme.Modules.pushforward ρ).obj (omegaA a)
  apply Scheme.Modules.hom_ext
  intro U
  ext t
  change (ModuleGlobalSections318.ofTop Z (0 : Γ(Z, ⊤))).val.app
      (op U) (show Γ(X, U) from t) = 0
  exact (ModuleGlobalSections318.ofTop_apply Z (0 : Γ(Z, ⊤)) U
    (show Γ(X, U) from t)).trans (by rw [map_zero, smul_zero])

include h in
theorem composite_zero : left σ ρ ≫ right σ ρ a h = 0 := by
  let u : (Scheme.Modules.pullback ρ).obj (unit X) ≅ unit A :=
    IdentityCotangent318.pullbackUnitIso ρ
  let p := IntrinsicDifferentialPullback318.map ρ a (xOverK σ) (fibre_over_k σ ρ a h)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction ρ
  have hp : rawLeft σ ≫ p = 0 := raw_composite_zero σ ρ a h
  have hn : (Scheme.Modules.pullback ρ).map (rawLeft σ) ≫ right σ ρ a h =
      (0 : (Scheme.Modules.pullback ρ).obj (unit X) ⟶ omegaA a) := by
    change (Scheme.Modules.pullback ρ).map (rawLeft σ) ≫ (adj.homEquiv _ _).symm p = _
    rw [← Adjunction.homEquiv_naturality_left_symm, hp, Adjunction.homEquiv_counit,
      Functor.map_zero, Limits.zero_comp]
  change (u.inv ≫ (Scheme.Modules.pullback ρ).map (rawLeft σ)) ≫ right σ ρ a h = _
  rw [Category.assoc, hn, Limits.comp_zero]

include h in
/-- The actual module complex, with no short exactness postulated. -/
noncomputable def moduleComplex : ShortComplex A.Modules :=
  ShortComplex.mk (left σ ρ) (right σ ρ a h) (composite_zero σ ρ a h)

include h in
/-- The very same row viewed in additive sheaves for the genuine H0 boundary.
The underlying-sheaf functor is additive; it is not an arbitrary functor input. -/
noncomputable def additiveComplex := by
  let F : A.Modules ⥤ Sheaf (_root_.Opens.grothendieckTopology (A : TopCat.{u}))
      AddCommGrpCat.{u} := SheafOfModules.toSheaf A.ringCatSheaf
  letI : F.PreservesZeroMorphisms := inferInstanceAs
    (SheafOfModules.toSheaf.{u} A.ringCatSheaf).PreservesZeroMorphisms
  exact (moduleComplex σ ρ a h).map F

end
end SelectedSameAActualFibreSheafArrows318
