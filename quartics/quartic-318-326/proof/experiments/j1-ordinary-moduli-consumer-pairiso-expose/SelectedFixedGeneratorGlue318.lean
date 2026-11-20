module
public import SelectedPrimitiveRootSignDescent318
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveRootSignDescent318

namespace SelectedFixedGeneratorGlue318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q)
variable (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => Fixed n I τ

/-- Same literal abscissa, now inside its genuine fixed algebra. -/
@[expose] def generator : F :=
  ⟨xbar n I,by
    change τ (xbar n I) = xbar n I
    simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_x] using
      (DFunLike.congr_fun hτ (SelectedPrimitiveAffineSign318.X n))⟩

local notation "x₀" => generator n I τ hτ

private theorem eval_to_quotient :
    F.val.comp (aeval x₀) = aeval (xbar n I) := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply,aeval_X] <;> rfl

/-- Every fixed element is a polynomial in the same algebro-geometric
abscissa, as an equality within the actual fixed subalgebra. -/
theorem generated (z : F) : ∃ p : R[X], aeval x₀ p = z := by
  have hz : τ (z:Q) = (z:Q) := z.property
  obtain ⟨p,hp⟩ := (fixed_iff_polynomial n I τ hτ (z:Q)).mp hz
  refine ⟨p,Subtype.ext ?_⟩
  change (F.val.comp (aeval x₀)) p = (z:Q)
  rwa [eval_to_quotient]

/-- Ring-map cancellation on the whole fixed ring follows from agreement
on base coefficients and on the single actual coordinate. -/
theorem ring_ext {T : Type*} [CommRing T] {f g : F →+* T}
    (hb : f.comp (algebraMap R F) = g.comp (algebraMap R F))
    (hx : f x₀ = g x₀) : f = g := by
  have hp : f.comp (aeval x₀).toRingHom = g.comp (aeval x₀).toRingHom := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro r
      change f (aeval x₀ (C r)) = g (aeval x₀ (C r))
      rw [aeval_C]
      exact DFunLike.congr_fun hb r
    · change f (aeval x₀ X) = g (aeval x₀ X)
      simpa only [aeval_X] using hx
  apply RingHom.ext
  intro z
  obtain ⟨p,rfl⟩ := generated n I τ hτ z
  exact DFunLike.congr_fun hp p

abbrev target := Spec (CommRingCat.of F)
abbrev targetBase : target n I τ ⟶ Spec (CommRingCat.of R) := Spec.algebraMap R F
abbrev sections (T : Scheme) := Scheme.Γ.obj (Opposite.op T)

/-- Read the actual polynomial generator as a global regular function
on an arbitrary Scheme test, not only on its geometric points. -/
@[expose] def read {T : Scheme} (f : T ⟶ target n I τ) : sections T :=
  ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ f.appTop) x₀

theorem read_natural {T U : Scheme} (f : T ⟶ target n I τ) (p : U ⟶ T) :
    read n I τ hτ (p ≫ f) = p.appTop (read n I τ hτ f) := by
  unfold read
  rw [Scheme.Hom.comp_appTop,←Category.assoc] <;> rfl

theorem read_spec {S : Type} [CommRing S] (f : F →+* S) :
    read n I τ hτ (Spec.map (CommRingCat.ofHom f)) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (f x₀) := by
  unfold read
  rw [←Scheme.ΓSpecIso_inv_naturality] <;> rfl

/-- A relative map to the actual sign chart cancels against a second map
if they have the same normalized generator as a regular section. -/
theorem scheme_ext {T : Scheme} {f g : T ⟶ target n I τ}
    (hb : f ≫ targetBase n I τ = g ≫ targetBase n I τ)
    (hx : read n I τ hτ f = read n I τ hτ g) : f = g := by
  apply AlgebraicGeometry.ext_to_Spec
  apply CommRingCat.hom_ext
  apply ring_ext n I τ hτ
  · apply RingHom.ext
    intro a
    have hb' (p : T ⟶ target n I τ) :
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p ≫ targetBase n I τ).appTop =
          CommRingCat.ofHom (algebraMap R F) ≫
            ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop) := by
      change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (p ≫ Spec.map (CommRingCat.ofHom (algebraMap R F))).appTop = _
      rw [Scheme.Hom.comp_appTop,←Category.assoc,←Scheme.ΓSpecIso_inv_naturality,Category.assoc]
    have h := congrArg (fun j : T ⟶ Spec (CommRingCat.of R) =>
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ j.appTop) a) hb
    rw [hb' f,hb' g] at h
    exact h
  · exact hx

section Glue
variable {T : Scheme} (b : T ⟶ Spec (CommRingCat.of R)) (cover : T.OpenCover)
variable (loc : ∀ i, cover.X i ⟶ target n I τ)
variable (hbase : ∀ i, loc i ≫ targetBase n I τ = cover.f i ≫ b)
variable (hx : ∀ i j,
  (pullback.fst (cover.f i) (cover.f j)).appTop (read n I τ hτ (loc i)) =
  (pullback.snd (cover.f i) (cover.f j)).appTop (read n I τ hτ (loc j)))

include hbase hx in
private theorem compatible (i j : cover.I₀) :
    pullback.fst (cover.f i) (cover.f j) ≫ loc i =
      pullback.snd (cover.f i) (cover.f j) ≫ loc j := by
  apply scheme_ext n I τ hτ
  · calc
      _ = (pullback.fst (cover.f i) (cover.f j) ≫ cover.f i) ≫ b := by
        rw [Category.assoc,hbase i,←Category.assoc]
      _ = _ := by
        rw [pullback.condition,Category.assoc,←hbase j,←Category.assoc]
  · rw [read_natural,read_natural]
    exact hx i j

/-- The sign class glues from its actual local maps once the regular
generator agrees on the genuine overlap; no compatibility on all
coordinates or blanket moduli theorem is assumed. -/
@[expose] def glued : T ⟶ target n I τ :=
  cover.glueMorphisms loc (compatible n I τ hτ b cover loc hbase hx)

@[reassoc] theorem glued_local (i : cover.I₀) :
    cover.f i ≫ glued n I τ hτ b cover loc hbase hx = loc i :=
  cover.ι_glueMorphisms _ _ i

theorem glued_over :
    glued n I τ hτ b cover loc hbase hx ≫ targetBase n I τ = b := by
  apply cover.hom_ext
  intro i
  rw [←Category.assoc,glued_local,hbase]

/-- Effective uniqueness after any actual open cover of a Scheme test. -/
theorem glued_unique (f : T ⟶ target n I τ)
    (hf : ∀ i, cover.f i ≫ f = loc i) :
    f = glued n I τ hτ b cover loc hbase hx := by
  apply cover.hom_ext
  intro i
  rw [hf,glued_local]

end Glue
end SelectedFixedGeneratorGlue318

#print axioms SelectedFixedGeneratorGlue318.scheme_ext
#print axioms SelectedFixedGeneratorGlue318.glued_unique
