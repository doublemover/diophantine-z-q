module
public import PELOriginalMultiplicationFppfCover318
public import PELOriginalRepresentedGroupFunctor318
public section
noncomputable section
namespace PELOriginalMultiplicationLocalEpimorphism318
open AlgebraicGeometry CategoryTheory Opposite
open PELOriginalSchemePointGroup318 PELOriginalRepresentedGroupFunctor318
open PELOriginalMultiplicationLocalDivision318 PELOriginalMultiplicationFppfCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)

/-- Multiplication on the genuine represented additive group presheaf,
with its original group laws on arbitrary complex scheme tests. -/
@[expose] def transformation : groupFunctor τ hτ ⟶ groupFunctor τ hτ where
  app T := AddCommGrpCat.ofHom
    { toFun := fun p => n • p
      map_zero' := zsmul_zero n
      map_add' := by intro p q; simp only [zsmul_add] }
  naturality T U f := by
    apply AddCommGrpCat.ext
    intro p
    exact (map_zsmul (pull τ hτ T.unop.hom f.unop.left f.unop.w) p n).symm

/-- This component is postcomposition by the SAME actual finite flat
multiplication morphism, not an independent presheaf endomorphism. -/
lemma original_map (T : Over (Spec (CommRingCat.of ℂ)))
    (p : Points τ hτ T.left T.hom) :
    ((transformation τ hτ n).app (op T) p).val=
      p.val≫PELOriginalIntegerMultiplication318.multiplication τ hτ n :=
  (PELOriginalIntegerMultiplication318.test_action τ hτ n p.val p.property).symm

/-- Genuine fppf-local surjectivity on ALL scheme tests. The image sieve
contains the explicitly constructed finite flat singleton cover. -/
lemma locally_surjective (hn : n≠0) :
    Presheaf.IsLocallySurjective
      (RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ)))
      (transformation τ hτ n) where
  imageSieve_mem {T} p := by
    apply (RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ))).superset_covering _
      (covering τ hτ n T.hom p hn)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    refine ⟨root τ hτ n T.hom p,?_⟩
    exact root_equation τ hτ n T.hom p

/-- Before sheafification the exact kernel at EVERY test is represented
by the actual scheme-theoretic equalizer. Local surjectivity above is a
separate fppf assertion, rather than false pointwise divisibility. -/
lemma kernel_iff {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ))
    (p : Points τ hτ T ρ) :
    (transformation τ hτ n).app (op (Over.mk ρ)) p=0 ↔
      ∃ q : PELOriginalTorsionKernelScheme318.KernelPoints τ hτ n T ρ,
        q.val≫PELOriginalTorsionKernelScheme318.inclusion τ hτ n=p.val := by
  constructor
  · intro hp
    let q := (PELOriginalTorsionKernelScheme318.pointsEquiv τ hτ n ρ).symm ⟨p,hp⟩
    refine ⟨q,?_⟩
    have he := (PELOriginalTorsionKernelScheme318.pointsEquiv τ hτ n ρ).apply_symm_apply ⟨p,hp⟩
    exact congrArg (fun a => a.val.val) he
  · rintro ⟨q,hq⟩
    have he : (PELOriginalTorsionKernelScheme318.pointsEquiv τ hτ n ρ q).val=p := by
      apply Subtype.ext
      exact hq
    change n • p=0
    rw [←he]
    exact (PELOriginalTorsionKernelScheme318.pointsEquiv τ hτ n ρ q).property
end PELOriginalMultiplicationLocalEpimorphism318
