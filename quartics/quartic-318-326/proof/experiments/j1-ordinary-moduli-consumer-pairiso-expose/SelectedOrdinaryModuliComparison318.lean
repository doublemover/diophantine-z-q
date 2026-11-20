module
public import SelectedOrdinaryMarkedModuli318
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open SelectedPrimitiveOpen318 SelectedLiteralTorsionKernel318
open SelectedMarkedNormalization318 SelectedCanonicalMarkedConverse318
open SelectedCanonicalCompletedConverse318 SelectedOrdinaryMarkedModuli318
open SelectedAffineMarkCoefficient318

namespace SelectedOrdinaryModuliComparison318
variable (n m : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "X" => Spec (CommRingCat.of F)
local notation "b" => Spec.algebraMap R F
local notation "P₀" => canonical n I τ hτ hY

private theorem literal_a_unit : IsUnit (A n) := by
  change IsUnit (-3*OpenJModel318.jCoord n*OpenJModel318.inverseDenominator n)
  exact (((OpenJModel318.base_units n).2.1.neg).mul
    (OpenJModel318.base_units n).2.2.2.1).mul ((OpenJModel318.denominatorUnit n)⁻¹).isUnit

private theorem literal_b_unit : IsUnit (B n) := by
  change IsUnit (-2*OpenJModel318.jCoord n*OpenJModel318.inverseDenominator n)
  exact (((OpenJModel318.base_units n).1.neg).mul
    (OpenJModel318.base_units n).2.2.2.1).mul ((OpenJModel318.denominatorUnit n)⁻¹).isUnit

variable {S : Type} [CommRing S] [Algebra R S]
variable (f g : F →ₐ[R] S)
local notation "d" v => Units.map v.toMonoidHom (twistUnit n I τ hτ hY)
local notation "P" v => P₀.change v.toRingHom
local notation "x₀" => fixedX n I τ hτ

private theorem changed_point_x : (P f).x = f (markX n I τ hτ hY) :=
  changed_x n I τ hτ hY S f

/-- A marked isomorphism of two pullbacks of the canonical pair forces
equality of both maps on the same fixed-ring generator. The field of a
geometric point is not used to test this equality. -/
theorem affine_rigidity (r : Sˣ) (ha : (P g).a = (r:S)^4*(P f).a)
    (hb : (P g).b = (r:S)^6*(P f).b)
    (hx : (P g).x = (r:S)^2*(P f).x) : f = g := by
  have ha' : (d g)^2 = r^4*(d f)^2 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val,Units.val_mul]
    apply ((literal_a_unit n).map (algebraMap R S)).mul_right_cancel
    have ha₀ : f (twistA n I τ hτ hY) = ((d f):S)^2*algebraMap R S (A n) := by
      simp only [twistA,map_mul,map_pow,AlgHom.commutes] <;> rfl
    have ha₁ : g (twistA n I τ hτ hY) = ((d g):S)^2*algebraMap R S (A n) := by
      simp only [twistA,map_mul,map_pow,AlgHom.commutes] <;> rfl
    change g (twistA n I τ hτ hY) = (r:S)^4*f (twistA n I τ hτ hY) at ha
    rw [ha₀,ha₁,←mul_assoc] at ha
    exact ha
  have hb' : (d g)^3 = r^6*(d f)^3 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val,Units.val_mul]
    apply ((literal_b_unit n).map (algebraMap R S)).mul_right_cancel
    have hb₀ : f (twistB n I τ hτ hY) = ((d f):S)^3*algebraMap R S (B n) := by
      simp only [twistB,map_mul,map_pow,AlgHom.commutes] <;> rfl
    have hb₁ : g (twistB n I τ hτ hY) = ((d g):S)^3*algebraMap R S (B n) := by
      simp only [twistB,map_mul,map_pow,AlgHom.commutes] <;> rfl
    change g (twistB n I τ hτ hY) = (r:S)^6*f (twistB n I τ hτ hY) at hb
    rw [hb₀,hb₁,←mul_assoc] at hb
    exact hb
  have hd : d g = r^2*d f := by
    calc
      _ = (d g)^3 * ((d g)^2)⁻¹ := by group
      _ = _ := by rw [ha',hb']; group
  have hx' : abscissa (d g) ((P g).x) = abscissa (d f) ((P f).x) := by
    rw [hd,hx]
    exact abscissa_transition (d f) r _
  rw [changed_point_x,changed_point_x,canonical_read,canonical_read] at hx'
  exact alg_ext n I τ hτ hx'.symm

variable [Nontrivial F] [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]
variable (hm : 1 < m) (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of Q))
variable (he : intoAffine n m hm = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
variable {Y : Scheme} (j : Y ⟶ Spec (CommRingCat.of R)) (M : Classifier n m j)
local notation "p" => forward n m I τ hτ hY hm e he j M

theorem affine_injective
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ p =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ p) : f = g := by
  have hp := forward_represents n m I τ hτ hY hm e he j M
  have h₁ := M.change_class f hp
  have h₂ := M.change_class g hp
  rw [h] at h₁
  obtain ⟨r,ha,hb,hx⟩ := M.short_transition h₁ h₂
  exact affine_rigidity n I τ hτ hY f g r ha hb hx

/-- Purely scheme-level detection of monomorphy by the genuine relative
affine tests. For each affine chart the R-algebra is the one given by
the actual composition to the literal j-line. -/
theorem forward_mono : Mono p := by
  constructor
  intro Z α β h
  refine Z.affineCover.hom_ext _ _ fun i => ?_
  let W := Z.affineCover.X i
  let K := Scheme.Γ.obj (Opposite.op W)
  let E := W.isoSpec
  let s := E.inv ≫ Z.affineCover.f i
  let α' : Spec K ⟶ X := s ≫ α
  let β' : Spec K ⟶ X := s ≫ β
  have h' : α' ≫ p = β' ≫ p := by
    simp only [α',β',Category.assoc,h]
  have hbase : α' ≫ b = β' ≫ b := by
    have hh := congrArg (fun t : Spec K ⟶ Y => t ≫ j) h'
    simpa only [Category.assoc,forward_over] using hh
  obtain ⟨k,hk⟩ := Spec.map_surjective (α' ≫ b)
  letI : Algebra R K := k.hom.toAlgebra
  have hα : α' ≫ b = Spec.algebraMap R K := hk.symm
  have hβ : β' ≫ b = Spec.algebraMap R K := hbase.symm.trans hα
  let f := AffineProductEvaluation318.toAlgHom α' hα
  let g := AffineProductEvaluation318.toAlgHom β' hβ
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) = α' :=
    AffineProductEvaluation318.map_toAlgHom α' hα
  have hg : Spec.map (CommRingCat.ofHom g.toRingHom) = β' :=
    AffineProductEvaluation318.map_toAlgHom β' hβ
  have hfg := affine_injective n m I τ hτ hY f g hm e he j M (by rw [hf,hg]; exact h')
  have hab : α' = β' := by rw [←hf,←hg,hfg]
  calc
    _ = E.hom ≫ α' := by simp [α',s,E]
    _ = E.hom ≫ β' := by rw [hab]
    _ = _ := by simp [β',s,E]

/-- One *actual* affine short chart of the universal marked family.
The primitive root-cover evaluation is the exact map obtained by inverse
scaling on the same equation. An arbitrary pair/map to Y is insufficient:
the given chart map has to classify this marked object. -/
structure Chart {S : Type} [CommRing S] [Algebra R S] (t : Spec (CommRingCat.of S) ⟶ Y) where
  pair : Pair S
  actual : M.represents t pair
  c : Sˣ
  y : Sˣ
  y_eq : (y:S) = pair.mark (ShortAffineJacobian318.y pair.a pair.b)
  a_eq : pair.a = (c:S)^2*algebraMap R S (A n)
  b_eq : pair.b = (c:S)^3*algebraMap R S (B n)
  rootEval : Q →ₐ[R] EvenContactEtale318.RootRing c
  root_x : rootEval (xbar n I) =
    (↑((SelectedRelativeAffineSignDescent318.rootUnit S c)⁻¹):EvenContactEtale318.RootRing c)^2 *
      algebraMap S (EvenContactEtale318.RootRing c) pair.x

variable {t : Spec (CommRingCat.of S) ⟶ Y} [Nontrivial S]
variable (C : Chart n m I j M t)

@[expose] def classRing : F →ₐ[R] S :=
  (class_exists n I τ hτ S C.c C.pair.x C.rootEval C.root_x).exists.choose

local notation "f₀" => classRing n m I τ hτ j M C
theorem classRing_x : f₀ x₀ = abscissa C.c C.pair.x :=
  (class_exists n I τ hτ S C.c C.pair.x C.rootEval C.root_x).exists.choose_spec

theorem local_recovery :
    Spec.map (CommRingCat.ofHom f₀.toRingHom) ≫ p = t := by
  have hx₀ := classRing_x n m I τ hτ j M C
  have hc := M.change_class f₀ (forward_represents n m I τ hτ hY hm e he j M)
  apply (M.equal_of_iso C.actual hc ?_).symm
  let e₀ := recoverIso n I τ hτ hY S f₀ C.pair.a C.pair.b C.pair.mark
    C.c C.y C.y_eq C.a_eq C.b_eq hx₀
  refine ⟨e₀,?_,?_,?_⟩
  · exact recover_over n I τ hτ hY S f₀ C.pair.a C.pair.b C.pair.mark C.c C.y C.y_eq C.a_eq C.b_eq hx₀
  · exact recover_zero n I τ hτ hY S f₀ C.pair.a C.pair.b C.pair.mark C.c C.y C.y_eq C.a_eq C.b_eq hx₀
  · exact recover_mark n I τ hτ hY S f₀ C.pair.a C.pair.b C.pair.mark C.c C.y C.y_eq C.a_eq C.b_eq hx₀

variable (U : Y.OpenCover) (L : U.I₀ → Type)
  [∀ i, CommRing (L i)] [∀ i, Algebra R (L i)] [∀ i, Nontrivial (L i)]
  (E : ∀ i, U.X i ≅ Spec (CommRingCat.of (L i)))
  (charts : ∀ i, Chart n m I j M ((E i).inv ≫ U.f i))

@[expose] def localInverse (i : U.I₀) : U.X i ⟶ X :=
  (E i).hom ≫ Spec.map (CommRingCat.ofHom (classRing n m I τ hτ j M (charts i)).toRingHom)

local notation "a" => localInverse n m I τ hτ j M U L E charts

@[reassoc] theorem localInverse_forward (i : U.I₀) : a i ≫ p = U.f i := by
  rw [localInverse,Category.assoc,local_recovery n m I τ hτ hY hm e he j M (charts i),
    Iso.hom_inv_id_assoc]

private theorem overlap_compat (i k : U.I₀) :
    pullback.fst (U.f i) (U.f k) ≫ a i = pullback.snd (U.f i) (U.f k) ≫ a k := by
  letI := forward_mono n m I τ hτ hY hm e he j M
  apply (cancel_mono p).mp
  rw [Category.assoc,Category.assoc,localInverse_forward,localInverse_forward,pullback.condition]

/-- The actual inverse is glued over the entire supplied ordinary open.
Affine-local isomorphisms are not supplied premises. -/
@[expose] def inverse : Y ⟶ X :=
  U.glueMorphisms a (by exact overlap_compat n m I τ hτ hY hm e he j M U L E charts)

local notation "k" => inverse n m I τ hτ hY hm e he j M U L E charts

theorem inverse_forward : k ≫ p = 𝟙 Y := by
  apply U.hom_ext
  intro i
  rw [←Category.assoc,inverse,U.ι_glueMorphisms,localInverse_forward,Category.comp_id]

/-- Canonical comparison to the genuine representing object supplied by
the restricted universal property on the literal ordinary open. -/
@[expose] def comparison : X ≅ Y where
  hom := p
  inv := k
  hom_inv_id := by
    letI := forward_mono n m I τ hτ hY hm e he j M
    apply (cancel_mono p).mp
    rw [Category.assoc,inverse_forward,Category.comp_id,Category.id_comp]
  inv_hom_id := inverse_forward n m I τ hτ hY hm e he j M U L E charts

theorem comparison_over :
    (comparison n m I τ hτ hY hm e he j M U L E charts).hom ≫ j = b :=
  forward_over n m I τ hτ hY hm e he j M

end SelectedOrdinaryModuliComparison318

#print axioms SelectedOrdinaryModuliComparison318.affine_rigidity
#print axioms SelectedOrdinaryModuliComparison318.forward_mono
#print axioms SelectedOrdinaryModuliComparison318.comparison_over
