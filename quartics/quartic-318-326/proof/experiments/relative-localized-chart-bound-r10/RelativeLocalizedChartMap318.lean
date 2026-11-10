module
public import RelativeLocalizedChartBound318
public section
noncomputable section
namespace RelativeLocalizedChartMap318
open CategoryTheory LaurentPolynomial RelativeLaurentScalar318
universe u
variable (R : Type u) [CommRing R]
  (f : Polynomial R →+* LaurentPolynomial R)
  (N : ModuleCat.{u} (Polynomial R)) (M : ModuleCat.{u} (LaurentPolynomial R))
  (e : (ModuleCat.extendScalars f).obj N ≅ M)
local instance : Module R N := Module.compHom N Polynomial.C
local instance : Module R M := coefficientModule R M
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal comparison applied to the original extension adjunction unit. -/
def value (x : N) : M :=
  e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x)

lemma value_smul (p : Polynomial R) (x : N) :
    value R f N M e (p • x) = f p • value R f N M e x := by
  have h := ((ModuleCat.extendRestrictScalarsAdj f).unit.app N).hom.map_smul p x
  change ((ModuleCat.extendRestrictScalarsAdj f).unit.app N (p • x) :
    (ModuleCat.extendScalars f).obj N) =
      f p • ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x :
        (ModuleCat.extendScalars f).obj N) at h
  unfold value
  rw [h]
  exact e.hom.hom.map_smul _ _

/-- Coefficient linearity is derived from the original adjunction map and
its literal polynomial/Laurent coefficient square, not supplied separately. -/
def map (hC : ∀ r : R, f (Polynomial.C r) = C r) : N →ₗ[R] M where
  toFun := value R f N M e
  map_add' x y := by simp only [value,map_add]
  map_smul' r x := by
    change value R f N M e ((Polynomial.C r) • x) =
      (C r : LaurentPolynomial R) • value R f N M e x
    rw [value_smul,hC]

lemma map_apply (hC : ∀ r : R, f (Polynomial.C r) = C r) (x : N) :
    map R f N M e hC x =
      e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x) := rfl

lemma map_polynomial (hC : ∀ r : R, f (Polynomial.C r) = C r)
    (p : Polynomial R) (x : N) :
    map R f N M e hC (p • x) = f p • map R f N M e hC x :=
  value_smul R f N M e p x

/-- Any previously constructed original geometric restriction agreeing
with the displayed unit square is literally this coefficient map. -/
lemma map_eq_original (hC : ∀ r : R, f (Polynomial.C r) = C r)
    (ρ : N → M)
    (hρ : ∀ x : N, e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x) = ρ x) :
    (map R f N M e hC : N → M) = ρ := by
  funext x
  exact hρ x
end RelativeLocalizedChartMap318
