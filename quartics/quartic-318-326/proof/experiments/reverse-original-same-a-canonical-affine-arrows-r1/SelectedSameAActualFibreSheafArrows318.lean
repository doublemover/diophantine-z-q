module

public import IntrinsicDifferentialPullback318
public import PulledCoordinateMaps318
public import ModuleTopExt318
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Basic

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
  have hp : pr k (eps k) = 0 := TrivSqZeroExt.fst_inr _
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
  let q := IntrinsicDifferentialPullback318.map ρ a (xOverK σ) (fibre_over_k σ ρ a h)
  have hv := IntrinsicDifferentialPullback318.map_D ρ a (xOverK σ)
    (fibre_over_k σ ρ a h) ⊤ (epsilonSection σ)
  change q.app ⊤ ((FamilyIntrinsicDifferentials318.D (xOverK σ)).d (epsilonSection σ)) =
    (FamilyIntrinsicDifferentials318.D a).d (ρ.appTop (epsilonSection σ)) at hv
  rw [epsilon_on_fibre_zero σ ρ a h, map_zero] at hv
  change ModuleGlobalSections318.ofTop _ ((FamilyIntrinsicDifferentials318.D (xOverK σ)).d
    (epsilonSection σ)) ≫ q = 0
  rw [ModuleTopMorphisms318.ofTop_comp, hv]
  apply ModuleTopExt318.ext
  change (ModuleGlobalSections318.ofTop _ 0).val.app (op ⊤) (show Γ(X, ⊤) from 1) = _
  rw [ModuleTopMorphisms318.ofTop_top_one]
  simp

include h in
theorem composite_zero : left σ ρ ≫ right σ ρ a h = 0 := by
  change ((IdentityCotangent318.pullbackUnitIso ρ).inv ≫
      (Scheme.Modules.pullback ρ).map (rawLeft σ)) ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction ρ).homEquiv _ _).symm
          (IntrinsicDifferentialPullback318.map ρ a (xOverK σ) (fibre_over_k σ ρ a h)) = 0
  rw [Category.assoc, ← Adjunction.homEquiv_naturality_left_symm, raw_composite_zero σ ρ a h]
  -- The actual pullback is additive; only its preservation of zero is used here.
  simp only [Adjunction.homEquiv_counit, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

include h in
/-- The actual module complex, with no short exactness postulated. -/
noncomputable def moduleComplex : ShortComplex A.Modules :=
  ShortComplex.mk (left σ ρ) (right σ ρ a h) (composite_zero σ ρ a h)

include h in
/-- The very same row viewed in additive sheaves for the genuine H0 boundary.
The underlying-sheaf functor is additive; it is not an arbitrary functor input. -/
noncomputable def additiveComplex :=
  (moduleComplex σ ρ a h).map (SheafOfModules.toSheaf A.ringCatSheaf)

end SelectedSameAActualFibreSheafArrows318
