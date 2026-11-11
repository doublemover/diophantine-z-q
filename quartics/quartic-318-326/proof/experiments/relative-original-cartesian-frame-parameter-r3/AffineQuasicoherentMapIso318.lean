module
public import OriginalLineAffineModel318
public section
namespace AffineQuasicoherentMapIso318
open AlgebraicGeometry CategoryTheory
universe u
variable (A : CommRingCat.{u}) {M N : (Spec A).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)

/-- Invertibility of the ACTUAL global section map implies invertibility
of the original quasicoherent map, through its literal tilde-Gamma counits. -/
lemma of_sections [IsIso (moduleSpecΓFunctor.map f)] : IsIso f := by
  have hn := (tilde.adjunction (R:=A)).counit.naturality f
  change (tilde.functor A).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at hn
  have he : f=inv M.fromTildeΓ ≫
      (tilde.functor A).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ := by
    apply (cancel_epi M.fromTildeΓ).mp
    simpa only [Category.assoc,IsIso.hom_inv_id_assoc] using hn.symm
  rw [he]
  infer_instance
end AffineQuasicoherentMapIso318
