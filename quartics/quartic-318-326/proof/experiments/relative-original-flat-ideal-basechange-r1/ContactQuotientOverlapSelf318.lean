module
public import ContactQuotientOverlapSchemeIso318
public section
noncomputable section
namespace ContactQuotientOverlapSelf318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientOverlapOpen318 ContactQuotientOverlapSchemeRule318
variable (c : Fin 4 → ℚˣ) (a : Chart) (n : ℕ)
lemma open_top : parameterOpen c a a n=⊤ := by
  apply top_unique
  intro x hx
  rw [FiniteFamilyAvoidanceOpen318.mem_locus]
  intro z hz
  change original c a (VaryingWordGlobalOriginalMap318.original ℚ (ring c a) (Fin n) z)∈Set.range (original c a)
  exact ⟨_,rfl⟩
instance inclusion_iso : IsIso (parameterOpen c a a n).ι := by
  rw [open_top]
  infer_instance
lemma point_identity (S : CommRingCat.{0}) [Algebra ℚ S] (x : Point c a a n S) :
    ContactQuotientOverlapPointEquiv318.transition c a a n S x=x := by
  let I := ContactQuotientOverlapPointEquiv318.recover c a a n S x
  have h : ContactQuotientOverlapEquiv318.equivalence c a a S n I=I := by
    apply Subtype.ext
    exact ContactQuotientTransferRecovery318.self c a S n I.val
  change classify c a a n S (ContactQuotientOverlapEquiv318.equivalence c a a S n I)=x
  rw [h]
  exact ContactQuotientOverlapPointEquiv318.classify_recover c a a n S x
lemma transition_identity : (ContactQuotientOverlapSchemeIso318.iso c a a n).hom=𝟙 _ := by
  apply RelativeAffineTestExt318.hom_ext ℚ (structureMap c a a n)
  intro S _ x
  let y := (pointTest c a a n S).symm x
  change y.val ≫ (ContactQuotientOverlapSchemeIso318.iso c a a n).hom=y.val ≫ 𝟙 _
  rw [ContactQuotientOverlapSchemeIso318.evaluate,point_identity,Category.comp_id]
end ContactQuotientOverlapSelf318
