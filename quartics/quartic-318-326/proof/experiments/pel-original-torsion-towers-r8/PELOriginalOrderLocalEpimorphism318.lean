module
public import PELOriginalOrderDivisionTorsorIso318
public import PELOriginalRepresentedGroupFunctor318
public section
noncomputable section
namespace PELOriginalOrderLocalEpimorphism318
open AlgebraicGeometry CategoryTheory Opposite PELPrincipalOrderCoordinates318
open PELOriginalSchemePointGroup318 PELOriginalRepresentedGroupFunctor318
open PELOriginalOrderLocalDivision318 PELOriginalOrderFppfDivision318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)

/-- The SAME original order action on the actual represented additive
group presheaf, retaining every complex scheme test. -/
@[expose] def transformation : groupFunctor τ hτ ⟶ groupFunctor τ hτ where
  app T := AddCommGrpCat.ofHom
    (PELOriginalUniversalOrderAction318.endomorphism τ hτ T.unop.hom a)
  naturality T U f := by
    apply AddCommGrpCat.ext
    intro p
    exact (congrArg (fun e => e p)
      (PELOriginalUniversalOrderAction318.naturality τ hτ T.unop.hom
        f.unop.left f.unop.w a)).symm

lemma original_map (T : Over (Spec (CommRingCat.of ℂ)))
    (p : Points τ hτ T.left T.hom) :
    ((transformation τ hτ a).app (op T) p).val=
      p.val≫PELOriginalOrderSchemeMorphism318.morphism τ hτ a := rfl

/-- The actual nonzero reduced-norm order endomorphism is fppf-locally
surjective, witnessed by its literal finite etale kernel torsor. -/
lemma locally_surjective (ha : PELOriginalOrderIntegralNorm318.norm a≠0) :
    Presheaf.IsLocallySurjective
      (RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ)))
      (transformation τ hτ a) where
  imageSieve_mem {T} p := by
    apply (RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ))).superset_covering _
      (covering τ hτ a T.hom p ha)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    refine ⟨root τ hτ a T.hom p,?_⟩
    exact root_equation τ hτ a T.hom p

/-- The kernel on every test is represented by the WHOLE original zero
fiber. Local surjectivity is separate and does not assert roots before covering. -/
lemma kernel_iff {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ))
    (p : Points τ hτ T ρ) :
    (transformation τ hτ a).app (op (Over.mk ρ)) p=0 ↔
      ∃ q : PELOriginalOrderKernelScheme318.KernelPoint τ hτ a ρ,
        q.val≫PELOriginalOrderKernelScheme318.inclusion τ hτ a=p.val := by
  constructor
  · intro hp
    let q := (PELOriginalOrderKernelScheme318.equivalence τ hτ a ρ).symm ⟨p,hp⟩
    refine ⟨q,?_⟩
    have he := (PELOriginalOrderKernelScheme318.equivalence τ hτ a ρ).apply_symm_apply ⟨p,hp⟩
    exact congrArg (fun b => b.val.val) he
  · rintro ⟨q,hq⟩
    have he : (PELOriginalOrderKernelScheme318.equivalence τ hτ a ρ q).val=p := by
      apply Subtype.ext
      exact hq
    change PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ a p=0
    rw [←he]
    exact (PELOriginalOrderKernelScheme318.equivalence τ hτ a ρ q).property
end PELOriginalOrderLocalEpimorphism318
