module
public import ContactBicanonicalProjectiveMap318
public section
noncomputable section
namespace ContactBicanonicalIndependence318
open AlgebraicGeometry CategoryTheory Opposite Polynomial
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
abbrev B (i : Fin 4) := ContactIntrinsicFrames318.BranchRing c i
abbrev L := SourceFractionField318.L c
local instance sourceField : Field (L c) := (KummerTensorField318.source_raw_field c).toField

/-- The ratio t is genuinely transcendental over Q on every whole branch ring. -/
theorem branch_polynomial_injective (i : Fin 4) :
    Function.Injective (Polynomial.aeval (R:=ℚ) (ContactBicanonicalRatios318.branchRatio c i)) := by
  intro p q hpq
  have h := congrArg (fun x => SourceOpenFractionField318.openEmbedding c
    (BranchOverlapLocalization318.toOpen c i x)) hpq
  change SourceOpenFractionField318.openEmbedding c (BranchOverlapLocalization318.toOpen c i
    ((Polynomial.aeval (ContactBicanonicalRatios318.branchRatio c i)).toRingHom p)) =
    SourceOpenFractionField318.openEmbedding c (BranchOverlapLocalization318.toOpen c i
    ((Polynomial.aeval (ContactBicanonicalRatios318.branchRatio c i)).toRingHom q)) at h
  rw [ContactBicanonicalProjectiveMap318.branch_polynomial] at h
  simp only [RingHom.comp_apply,BranchOverlapLocalization318.toOpen_on_source,
    SourceOpenFractionField318.openEmbedding_on_order,SourceFractionField318.embedding_on_polynomial] at h
  exact (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) ((algebraMap (RatFunc ℚ) (L c)).injective h)

theorem ratio_linear_independent (i : Fin 4) (a b : ℚ)
    (h : algebraMap ℚ (B c i) a + algebraMap ℚ (B c i) b *
      ContactBicanonicalRatios318.branchRatio c i=0) : a=0 ∧ b=0 := by
  have hp : C a+C b*X=(0:ℚ[X]) := (branch_polynomial_injective c i) (by
    simpa only [map_add,map_mul,Polynomial.aeval_C,Polynomial.aeval_X,map_zero] using h)
  exact ⟨by simpa using congrArg (fun p : ℚ[X] => p.coeff 0) hp,
    by simpa using congrArg (fun p : ℚ[X] => p.coeff 1) hp⟩

/-- Rational constants are supplied by the actual Q-structure morphism. -/
@[expose] def constants : ℚ →+* Γ(ContactGlobalSmooth318.Model c,⊤) :=
  (ContactIntrinsicDifferentials318.structureMap c).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom

@[expose] def branchFunction (i : Fin 4) :
    B c i →+* Γ(ContactGlobalSmooth318.Model c,ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) :=
  ((ContactIntrinsicFrames318.branchEmbedding c i).appIso ⊤).inv.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (B c i))).inv.hom

theorem branchFunction_injective (i : Fin 4) : Function.Injective (branchFunction c i) :=
  (ConcreteCategory.bijective_of_isIso ((ContactIntrinsicFrames318.branchEmbedding c i).appIso ⊤).inv).1.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (B c i))).inv).1

theorem constants_restrict (i : Fin 4) (a : ℚ) :
    (ContactGlobalSmooth318.Model c).presheaf.map (homOfLE (show
      ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤ ≤ ⊤ from le_top)).op
      (constants c a)=branchFunction c i (algebraMap ℚ (B c i) a) := by
  exact DFunLike.congr_fun (RingHom.ext_rat
    (((ContactGlobalSmooth318.Model c).presheaf.map (homOfLE (show
      ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤ ≤ ⊤ from le_top)).op).hom.comp (constants c))
    ((branchFunction c i).comp (algebraMap ℚ (B c i)))) a

/-- Actual rational linear independence of the two global bicanonical sections.
The scalar action is explicitly the one from the actual Q-structure map. -/
theorem global_linear_independent (a b : ℚ)
    (h : constants c a • ContactGlobalBicanonical318.q0 c +
      constants c b • ContactGlobalBicanonical318.q1 c=0) : a=0 ∧ b=0 := by
  let U := ContactIntrinsicFrames318.branchEmbedding c (0:Fin 4) ''ᵁ ⊤
  have e := congrArg ((ContactGlobalBicanonical318.tensor c).presheaf.map
    (homOfLE (show U ≤ ⊤ from le_top)).op) h
  simp only [map_add,Scheme.Modules.map_smul,map_zero] at e
  rw [ContactBicanonicalSectionRatios318.global_branch_relation c 0,smul_smul,←add_smul] at e
  have he := (ContactBicanonicalGenerators318.global_branch_generator c 0 U le_rfl).1
    (e.trans (zero_smul _ _).symm)
  rw [constants_restrict,constants_restrict] at he
  change branchFunction c 0 (algebraMap ℚ (B c 0) a)+
    branchFunction c 0 (algebraMap ℚ (B c 0) b)*
      branchFunction c 0 (ContactBicanonicalRatios318.branchRatio c 0)=0 at he
  have hr := (branchFunction_injective c 0) (show branchFunction c 0
    (algebraMap ℚ (B c 0) a+algebraMap ℚ (B c 0) b*ContactBicanonicalRatios318.branchRatio c 0)=
      branchFunction c 0 0 by simpa only [map_add,map_mul,map_zero] using he)
  exact ratio_linear_independent c 0 a b hr
end ContactBicanonicalIndependence318
