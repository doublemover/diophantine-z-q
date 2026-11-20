module
public import SelectedCanonicalCompletedConverse318
public import SelectedTwistGeometricOrder318
public import AffineProductEvaluation318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open SelectedPrimitiveOpen318 SelectedLiteralTorsionKernel318 SelectedSignedMultiplication318
open SelectedAffineMarkCoefficient318 SelectedMarkedNormalization318
open SelectedCanonicalMarkedConverse318 SelectedCanonicalCompletedConverse318

namespace SelectedOrdinaryMarkedModuli318

/-- Literal relative short equations and their actual finite marked section.
Eligibility as an elliptic curve with this level is a separate proposition. -/
structure Pair (S : Type) [CommRing S] where
  a : S
  b : S
  mark : ShortAffineJacobian318.Ring a b →ₐ[S] S

abbrev Pair.curve {S : Type} [CommRing S] (P : Pair S) := scheme P.a P.b
abbrev Pair.section {S : Type} [CommRing S] (P : Pair S) := point P.a P.b P.mark
abbrev Pair.x {S : Type} [CommRing S] (P : Pair S) := P.mark (ShortAffineJacobian318.x P.a P.b)

@[expose] def Pair.change {S T : Type} [CommRing S] [CommRing T]
    (f : S →+* T) (P : Pair S) : Pair T := by
  letI : Algebra S T := f.toAlgebra
  exact ⟨f P.a,f P.b,extendEval P.a P.b ((Algebra.ofId S T).comp P.mark)⟩

/-- The genuine completed isomorphism, over the identity on the base,
preserving both zero and the actual marked section. -/
@[expose] def PairIso {S : Type} [CommRing S] (P Q : Pair S) : Prop :=
  ∃ e : P.curve ≅ Q.curve,
    e.hom ≫ structureMap Q.a Q.b = structureMap P.a P.b ∧
    infinity P.a P.b ≫ e.hom = infinity Q.a Q.b ∧
    P.section ≫ e.hom = Q.section

variable (n m : ℕ)
local notation "R" => SelectedPrimitiveAffineSign318.R n

/-- Same j on this literal j-base, full [m] equation and exact order
on every geometric fiber. There is no global lower-order condition on
a disconnected test ring. -/
def Eligible {S : Type} [CommRing S] [Algebra R S] (P : Pair S) : Prop :=
  ∃ h : IsUnit (-16*(4*P.a^3+27*P.b^2)),
    (-48*P.a)^3 = algebraMap R S (OpenJModel318.jCoord n) * (-16*(4*P.a^3+27*P.b^2)) ∧
    Killed h m P.section ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K]
      (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S)),
        ExactTests h m (t ≫ P.section)

/-- Restricted universal-property input on the genuine ordinary locus:
existence on eligible literal pairs, base change of their class, and
equality of classes exactly as used in the comparison. This does not
assert any isomorphism with the literal invariant-ring chart. -/
structure Classifier {Y : Scheme} (j : Y ⟶ Spec (CommRingCat.of R)) where
  represents : ∀ {S : Type} [CommRing S] [Algebra R S],
    (Spec (CommRingCat.of S) ⟶ Y) → Pair S → Prop
  over : ∀ {S : Type} [CommRing S] [Algebra R S] {t : Spec (CommRingCat.of S) ⟶ Y} {P : Pair S},
    represents t P → t ≫ j = Spec.algebraMap R S
  exists_class : ∀ {S : Type} [CommRing S] [Algebra R S] (P : Pair S),
    Eligible n m P → ∃ t, represents t P
  change_class : ∀ {S T : Type} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) {t : Spec (CommRingCat.of S) ⟶ Y} {P : Pair S},
    represents t P →
      represents (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ t) (P.change f.toRingHom)
  equal_of_iso : ∀ {S : Type} [CommRing S] [Algebra R S]
    {f g : Spec (CommRingCat.of S) ⟶ Y} {P Q : Pair S},
    represents f P → represents g Q → PairIso P Q → f = g
  short_transition : ∀ {S : Type} [CommRing S] [Algebra R S]
    {f : Spec (CommRingCat.of S) ⟶ Y} {P Q : Pair S},
    represents f P → represents f Q → ∃ r : Sˣ,
      Q.a = (r:S)^4*P.a ∧ Q.b = (r:S)^6*P.b ∧ Q.x = (r:S)^2*P.x

variable (I : Ideal (D n))
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "X" => Spec (CommRingCat.of F)
local notation "base" => Spec.algebraMap R F

@[expose] def canonical : Pair F :=
  ⟨twistA n I τ hτ hY,twistB n I τ hτ hY,markEvaluation n I τ hτ hY⟩
local notation "P₀" => canonical n I τ hτ hY

private theorem literal_j :
    (-48*A n)^3 = OpenJModel318.jCoord n * (-16*(4*(A n)^3+27*(B n)^2)) := by
  rw [OpenJAffineScheme318.actual_discriminant]
  have h := OpenJModel318.c4_cube (OpenJModel318.jCoord n) (OpenJModel318.inverseDenominator n)
    (OpenJModel318.denominator_inverse n)
  rw [OpenJModel318.c4] at h
  unfold A OpenJAffineScheme318.A
  convert h using 1 <;> ring

theorem canonical_j :
    (-48*P₀.a)^3 = algebraMap R F (OpenJModel318.jCoord n) * (-16*(4*P₀.a^3+27*P₀.b^2)) := by
  let d := (twistUnit n I τ hτ hY : Fˣ)
  have h := congrArg (algebraMap R F) (literal_j n)
  simp only [map_neg,map_mul,map_pow,map_add,map_ofNat] at h
  change (-48*((d:F)^2*algebraMap R F (A n)))^3 =
    algebraMap R F (OpenJModel318.jCoord n) *
      (-16*(4*((d:F)^2*algebraMap R F (A n))^3+27*((d:F)^3*algebraMap R F (B n))^2))
  linear_combination (d:F)^6*h

variable [hF : Nontrivial F] [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]
variable (hm : 1 < m) (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of Q))
variable (he : intoAffine n m hm = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

include hF hm e he in
theorem canonical_eligible : Eligible n m P₀ := by
  refine ⟨disc_unit n I τ hτ hY,canonical_j n I τ hτ hY,?_,?_⟩
  · exact SelectedTwistExactOrder318.killed n I τ hτ hY m hm e he
  · intro K _ _ t
    exact SelectedTwistGeometricOrder318.exact_geometric n I τ hτ hY m hm e he t

variable {Y : Scheme} (j : Y ⟶ Spec (CommRingCat.of R)) (M : Classifier n m j)

/-- The actual forward map over the ordinary j-line is obtained by
classifying the already constructed, actual exact-order canonical pair. -/
@[expose] def forward : X ⟶ Y :=
  (M.exists_class P₀ (canonical_eligible n m I τ hτ hY hm e he)).choose

local notation "p" => forward n m I τ hτ hY hm e he j M
theorem forward_represents : M.represents p P₀ :=
  (M.exists_class P₀ (canonical_eligible n m I τ hτ hY hm e he)).choose_spec

theorem forward_over : p ≫ j = base := M.over (forward_represents n m I τ hτ hY hm e he j M)

end SelectedOrdinaryMarkedModuli318

#print axioms SelectedOrdinaryMarkedModuli318.canonical_eligible
#print axioms SelectedOrdinaryMarkedModuli318.forward_over
