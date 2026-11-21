module
public import SelectedIntrinsicBaseLinear318
public import SelectedIntrinsicGlobalToAffine318
public import IntrinsicDifferentialSectionPullback318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory
open SelectedIntrinsicGlobalToAffine318

namespace SelectedCompactDifferentialSquare318
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]
variable {X Y : Scheme.{u}}
variable (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
variable (f : X ⟶ Y) (hf : f ≫ q = p)
variable (a : S →ₐ[R] T)
variable (i : Spec (CommRingCat.of T) ⟶ X) [IsOpenImmersion i]
variable (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
variable (hi : i ≫ p = Spec.algebraMap R T) (hj : j ≫ q = Spec.algebraMap R S)

/-- Whole global pullback followed by the genuine affine restriction
is the Kähler map of the actual affine square on the same section. -/
theorem restrict_square (hs : i ≫ f = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ j)
    (ω : Γ(FamilyIntrinsicDifferentials318.omega q,⊤)) :
    restrict i p hi (IntrinsicDifferentialPullback318.globalSection f p q hf ω) =
      AlgHomDifferential318.map a (restrict j q hj ω) := by
  have hv := AffineChartPullbackScalars318.image_le f i j _ hs
  have hn := DFunLike.congr_fun
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p q hf a i j hi hj hs hv)
      (restrict j q hj ω)
  simp only [AddMonoidHom.comp_apply] at hn
  rw [restrict_norm] at hn
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective i p hi).injective
  rw [restrict_norm]
  exact (IntrinsicDifferentialSectionPullback318.globalSection_restrict f p q hf
    (j ''ᵁ ⊤) (i ''ᵁ ⊤) hv ω).symm.trans hn

private theorem kaehler_id (ω : KaehlerDifferential R S) :
    AlgHomDifferential318.map (AlgHom.id R S) ω = ω := by
  have h : (AlgHomDifferential318.map (AlgHom.id R S)).toAddMonoidHom =
      AddMonoidHom.id (KaehlerDifferential R S) := by
    apply KaehlerAdditiveExt318.ext
    · intro a
      exact AlgHomDifferential318.map_D (AlgHom.id R S) a
    · intro a x hx
      change AlgHomDifferential318.map (AlgHom.id R S) x = x at hx
      change AlgHomDifferential318.map (AlgHom.id R S) (a • x) = a • x
      rw [AlgHomDifferential318.map_smul,AlgHom.id_apply,hx]
  exact DFunLike.congr_fun h ω

variable (e : X ≅ Y) (he : e.hom ≫ q = p)
variable (i₀ : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion i₀]
variable (hi₀ : i₀ ≫ p = Spec.algebraMap R S)

/-- No choice of differential frames enters here: the two compact
incarnations restrict to the identical universal Kähler element in the
one actual chart, under the exact compact comparison. -/
theorem restrict_same (hs : i₀ ≫ e.hom = j) (ω : SelectedIntrinsicBaseLinear318.Sections q) :
    restrict i₀ p hi₀ (SelectedIntrinsicBaseLinear318.linearPullback p q e he ω) =
      restrict j q hj ω := by
  have h : i₀ ≫ e.hom = Spec.map (CommRingCat.ofHom (AlgHom.id R S).toRingHom) ≫ j := by
    change i₀ ≫ e.hom = Spec.map (𝟙 (CommRingCat.of S)) ≫ j
    rw [Spec.map_id,Category.id_comp,hs]
  let ω' : Γ(FamilyIntrinsicDifferentials318.omega q,⊤) := ω
  have hω : (show Γ(FamilyIntrinsicDifferentials318.omega p,⊤) from
      SelectedIntrinsicBaseLinear318.linearPullback p q e he ω) =
      IntrinsicDifferentialPullback318.globalSection e.hom p q he ω' :=
    SelectedIntrinsicBaseLinear318.linearPullback_apply p q e he ω
  exact (congrArg (restrict i₀ p hi₀) hω).trans
    ((restrict_square p q e.hom he (AlgHom.id R S) i₀ j hi₀ hj h ω').trans
      (kaehler_id (restrict j q hj ω')))

end SelectedCompactDifferentialSquare318

#print axioms SelectedCompactDifferentialSquare318.restrict_square
#print axioms SelectedCompactDifferentialSquare318.restrict_same
