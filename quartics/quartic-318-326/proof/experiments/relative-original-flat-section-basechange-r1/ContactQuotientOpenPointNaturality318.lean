module
public import ContactQuotientOverlapPointEquiv318
public section
noncomputable section
namespace ContactQuotientOpenPointNaturality318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientOverlapOpen318 ContactQuotientOverlapPointEquiv318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
  (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T] (φ : S →ₐ[ℚ] T)
@[expose] def map (x : Point c a b n S) : Point c a b n T :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.val,by
    rw [Category.assoc,Category.assoc,x.property]
    exact VaryingSourceCoefficientPullback318.coefficient_base ℚ S T φ⟩
lemma underlying_map (x : Point c a b n S) : underlying c a b n T (map c a b n S T φ x)=
    VaryingParameterPoint318.map ℚ (ring c a) (Fin n) S T φ (underlying c a b n S x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _
lemma underlying_injective : Function.Injective (underlying c a b n S) := by
  intro x y h
  apply Subtype.ext
  apply (cancel_mono (parameterOpen c a b n).ι).mp
  exact congrArg Subtype.val h
lemma classify_natural (I : ContactQuotientOverlapEquiv318.Overlap c a b S n) :
    classify c a b n T (ContactQuotientOverlapNaturality318.map c a b S T φ n I)=
      map c a b n S T φ (classify c a b n S I) := by
  apply underlying_injective c a b n T
  rw [classify_underlying,underlying_map,classify_underlying]
  exact VaryingProjectiveQuotientNaturality318.classify_natural ℚ (ring c a) (Fin n) S T φ I.val
lemma recover_natural (x : Point c a b n S) : recover c a b n T (map c a b n S T φ x)=
    ContactQuotientOverlapNaturality318.map c a b S T φ n (recover c a b n S x) := by
  apply (equivalence c a b n T).injective
  change classify c a b n T (recover c a b n T (map c a b n S T φ x))=
    classify c a b n T (ContactQuotientOverlapNaturality318.map c a b S T φ n (recover c a b n S x))
  rw [classify_recover,classify_natural,classify_recover]
/-- The exact open-point transition is natural for EVERY rational
coefficient algebra map, including nonflat and nilpotent changes. -/
lemma transition_natural (x : Point c a b n S) : transition c a b n T (map c a b n S T φ x)=
    map c b a n S T φ (transition c a b n S x) := by
  change classify c b a n T (ContactQuotientOverlapEquiv318.equivalence c a b T n
    (recover c a b n T (map c a b n S T φ x)))=
      map c b a n S T φ (classify c b a n S (ContactQuotientOverlapEquiv318.equivalence c a b S n
        (recover c a b n S x)))
  rw [recover_natural,ContactQuotientOverlapNaturality318.natural,classify_natural]
end ContactQuotientOpenPointNaturality318
