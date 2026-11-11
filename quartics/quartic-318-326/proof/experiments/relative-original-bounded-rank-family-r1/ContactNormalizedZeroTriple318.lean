module
public import ContactNormalizedZeroOverlap318
public import ProjectiveParameterSliceTriplePoints318
public import ContactGlobalZeroClosed318
public section
noncomputable section
namespace ContactNormalizedZeroTriple318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ProjectiveParameterSliceTriplePoints318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local notation "N" => L' R S f c L
variable {i j k : Fin F.size}

/-- Literal zeros of the classified original section on an arbitrary
coefficient test. All three normalized points use the SAME pulled line. -/
abbrev zero (a : Point R P S i j k) : Scheme :=
  ContactGlobalSectionZero318.scheme S c N
    (ContactOriginalSectionParameter318.points R c L hz S f a.point)
@[expose] def into (a : Point R P S i j k) : zero R c L hz S f a ⟶ curve S c :=
  ContactGlobalSectionZero318.into S c N
    (ContactOriginalSectionParameter318.points R c L hz S f a.point)
instance into_mono (a : Point R P S i j k) : Mono (into R c L hz S f a) := inferInstance

/-- Scheme-level normalized transition, not merely the transition on
its parameter points. Its full original closed embedding is preserved. -/
@[expose] def rotation (a : Point R P S i j k) :
    zero R c L hz S f (rotate R P S i j k a) ≅ zero R c L hz S f a :=
  ContactParameterUnitZeros318.zeroIso R c L hz S f a.secondUnit⁻¹ a.point
@[reassoc] lemma rotation_into (a : Point R P S i j k) :
    (rotation R c L hz S f a).hom ≫ into R c L hz S f a=
      into R c L hz S f (rotate R P S i j k a) :=
  ContactParameterUnitZeros318.zeroIso_into R c L hz S f a.secondUnit⁻¹ a.point

private lemma equality_into {a b : Point R P S i j k} (h : a=b) :
    eqToHom (congrArg (zero R c L hz S f) h) ≫ into R c L hz S f b=
      into R c L hz S f a := by
  subst b
  simp only [eqToHom_refl,Category.id_comp]

/-- Actual scheme arrows satisfy the cyclic triple normalization law.
The final equality follows from the original closed-immersion mono,
so no arbitrary choice of zero-scheme isomorphism survives the cycle.
The only transport is the ALREADY PROVED equality of the three actual
normalized parameter points, valid on all coefficient rings. -/
lemma cycle (a : Point R P S i j k) :
    (rotation R c L hz S f (rotate R P S j k i (rotate R P S i j k a))).hom ≫
      (rotation R c L hz S f (rotate R P S i j k a)).hom ≫
      (rotation R c L hz S f a).hom=
    eqToHom (congrArg (zero R c L hz S f) (rotate_three R P S i j k a)) := by
  apply (cancel_mono (into R c L hz S f a)).1
  rw [Category.assoc,Category.assoc,rotation_into,rotation_into,rotation_into,
    equality_into]

/-- Any two candidates with the same original closed embedding agree.
This is the uniqueness statement used when transporting these explicit
cyclic comparisons to the genuine localized triple-overlap schemes. -/
lemma unique {a b : Point R P S i j k}
    (v w : zero R c L hz S f a ⟶ zero R c L hz S f b)
    (hv : v ≫ into R c L hz S f b=into R c L hz S f a)
    (hw : w ≫ into R c L hz S f b=into R c L hz S f a) : v=w :=
  (cancel_mono (into R c L hz S f b)).1 (hv.trans hw.symm)
end ContactNormalizedZeroTriple318
