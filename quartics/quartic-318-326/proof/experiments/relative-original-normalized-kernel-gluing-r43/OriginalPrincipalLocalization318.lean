module
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace OriginalPrincipalLocalization318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable (X : Scheme.{u})
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original structure-sheaf restriction, with its genuine ring structure. -/
abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X,U) →+* Γ(X,V) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma res_res {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : Γ(X,U)) :
    res X k (res X h s) = res X (k.trans h) s := by
  change X.presheaf.map _ (X.presheaf.map _ s) = _
  rw [← X.presheaf.map_comp_apply]
  rfl

/-- The actual global coefficient on any original open. -/
abbrev coefficient (U : X.Opens) (s : Γ(X,⊤)) : Γ(X,U) := res X le_top s

lemma res_coefficient {U V : X.Opens} (h : V ≤ U) (s : Γ(X,⊤)) :
    res X h (coefficient X U s) = coefficient X V s := res_res X le_top h s

/-- Actual restriction from an affine open to its intersection with a
principal global open is localization away from the SAME restricted
coefficient. This holds for arbitrary, including nonreduced, schemes. -/
theorem localization (U : X.Opens) (hU : IsAffineOpen U) (s : Γ(X,⊤)) :
    @IsLocalization.Away (Γ(X,U)) _ (coefficient X U s)
      (Γ(X,X.basicOpen s ⊓ U)) _ (res X (inf_le_right : X.basicOpen s ⊓ U ≤ U)).toAlgebra := by
  apply hU.isLocalization_of_eq_basicOpen (coefficient X U s)
    (homOfLE (inf_le_right : X.basicOpen s ⊓ U ≤ U))
  change X.basicOpen s ⊓ U = X.basicOpen (X.presheaf.map (homOfLE le_top).op s)
  rw [Scheme.basicOpen_res,inf_comm]

/-- Clear a denominator in the ORIGINAL section ring, with no injection
into a fraction field and no assumption that s is regular or nonzero. -/
theorem clear (U : X.Opens) (hU : IsAffineOpen U) (s : Γ(X,⊤))
    (z : Γ(X,X.basicOpen s ⊓ U)) :
    ∃ n : ℕ, ∃ a : Γ(X,U),
      (coefficient X (X.basicOpen s ⊓ U) s)^n * z = res X inf_le_right a := by
  letI : Algebra (Γ(X,U)) (Γ(X,X.basicOpen s ⊓ U)) := (res X inf_le_right).toAlgebra
  letI : IsLocalization.Away (coefficient X U s) (Γ(X,X.basicOpen s ⊓ U)) :=
    localization X U hU s
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj (coefficient X U s) z
  refine ⟨n,a,?_⟩
  change z * (res X inf_le_right (coefficient X U s))^n = res X inf_le_right a at ha
  rw [res_coefficient] at ha
  exact (mul_comm _ _).trans ha

/-- Equality after the original principal restriction is killed by a
finite power on the original larger open. This replaces the invalid
fraction-field injection on nonreduced bases. -/
theorem kill (U : X.Opens) (hU : IsAffineOpen U) (s : Γ(X,⊤))
    (a : Γ(X,U)) (ha : res X (inf_le_right : X.basicOpen s ⊓ U ≤ U) a = 0) :
    ∃ n : ℕ, (coefficient X U s)^n * a = 0 := by
  letI : Algebra (Γ(X,U)) (Γ(X,X.basicOpen s ⊓ U)) := (res X inf_le_right).toAlgebra
  letI : IsLocalization.Away (coefficient X U s) (Γ(X,X.basicOpen s ⊓ U)) :=
    localization X U hU s
  have hh : algebraMap (Γ(X,U)) (Γ(X,X.basicOpen s ⊓ U)) a =
      algebraMap (Γ(X,U)) (Γ(X,X.basicOpen s ⊓ U)) 0 := by
    change res X inf_le_right a = res X inf_le_right 0
    simpa only [map_zero] using ha
  obtain ⟨n,hn⟩ := IsLocalization.Away.exists_of_eq (coefficient X U s) hh
  exact ⟨n,by simpa only [mul_zero] using hn⟩
end OriginalPrincipalLocalization318
