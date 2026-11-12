module
public import StableOpenSectionLaws318
public section
noncomputable section
namespace InvariantMorphismSectionPullback318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Z:Scheme.{u}}

lemma appLE_morphism_congr {f g:X⟶Z} (h:f=g) (V:Z.Opens) (W:X.Opens)
    (hf:W≤f⁻¹ᵁV) (hg:W≤g⁻¹ᵁV):f.appLE V W hf=g.appLE V W hg:=by
  subst g
  rfl

/-- An invariant SCHEME map has invariant actual section pullbacks on
any suitable stable open, by native composition, not only on field germs. -/
lemma appLE_fixed (a:X⟶X) (g:X⟶Z) (h:a≫g=g) (V:Z.Opens) (W:X.Opens)
    (eg:W≤g⁻¹ᵁV) (ea:W≤a⁻¹ᵁW):
    g.appLE V W eg≫a.appLE W W ea=g.appLE V W eg:=by
  exact (Scheme.Hom.appLE_comp_appLE a g V W W eg ea).trans
    (appLE_morphism_congr h V W _ eg)
end InvariantMorphismSectionPullback318
