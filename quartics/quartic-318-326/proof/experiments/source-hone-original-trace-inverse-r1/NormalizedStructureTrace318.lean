module
public import StructureAdditiveSheaf318

public section
noncomputable section
namespace NormalizedStructureTrace318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open StructureAdditiveSheaf318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme} (f : X ⟶ Y)
  (q : Y ⟶ Spec (CommRingCat.of ℚ))

/-- Rational constants on every open come from the original structure map. -/
@[expose] def scalar (U : Y.Opens) : ℚ →+* Γ(Y, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ q.appTop ≫
    Y.presheaf.map (homOfLE le_top).op).hom

theorem scalar_restrict {U V : Y.Opens} (j : U ⟶ V) (a : ℚ) :
    Y.presheaf.map j.op (scalar q V a) = scalar q U a := by
  change (((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ q.appTop ≫
    Y.presheaf.map (homOfLE le_top).op ≫ Y.presheaf.map j.op) :
      CommRingCat.of ℚ ⟶ Γ(Y, U)) a = _
  rw [← Functor.map_comp]
  rfl

theorem eighth_mul (U : Y.Opens) : scalar q U (1/8) * (8 : Γ(Y, U)) = 1 := by
  have h := congrArg (scalar q U) (by norm_num : (1/8 : ℚ) * 8 = 1)
  simpa only [map_mul, map_ofNat, map_one] using h

/-- The actual trace normalized by its degree, as a sheaf morphism on all opens. -/
@[expose] def retraction (t : pushed f ⟶ sheaf Y) : pushed f ⟶ sheaf Y :=
  ⟨{
    app U := AddCommGrpCat.ofHom {
      toFun s := scalar q U.unop (1/8) * (show Γ(Y, U.unop) from t.hom.app U s)
      map_zero' := by rw [map_zero, mul_zero]
      map_add' a b := by rw [map_add, mul_add] }
    naturality U V j := by
      ext s
      change scalar q V.unop (1/8) *
        (show Γ(Y, V.unop) from t.hom.app V ((pushed f).obj.map j s)) =
        Y.presheaf.map j (scalar q U.unop (1/8) * (show Γ(Y, U.unop) from t.hom.app U s))
      have hc : Y.presheaf.map j (scalar q U.unop (1/8)) = scalar q V.unop (1/8) :=
        scalar_restrict q j.unop (1/8)
      have hs : (show Γ(Y, V.unop) from t.hom.app V ((pushed f).obj.map j s)) =
          Y.presheaf.map j (show Γ(Y, U.unop) from t.hom.app U s) :=
        congrArg (fun k => k s) (t.hom.naturality j)
      exact (congrArg₂ (fun a b : Γ(Y, V.unop) => a * b) hc.symm hs).trans
        ((Y.presheaf.map j).hom.map_mul _ _).symm
  }⟩

theorem retraction_component (t : pushed f ⟶ sheaf Y) (U : Y.Opens)
    (s : Γ(X, f ⁻¹ᵁ U)) :
    (retraction f q t).hom.app (op U) s =
      scalar q U (1/8) * (show Γ(Y, U) from t.hom.app (op U) s) := rfl

/-- The actual full-open degree-eight identity gives a genuine sheaf retraction. -/
theorem pullback_retraction (t : pushed f ⟶ sheaf Y)
    (h : ∀ (U : Y.Opens) (s : Γ(Y, U)), t.hom.app (op U) (f.app U s) = 8 * s) :
    pullback f ≫ retraction f q t = 𝟙 (sheaf Y) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change scalar q U.unop (1/8) * (show Γ(Y, U.unop) from t.hom.app U (f.app U.unop s)) = s
  rw [h, ← mul_assoc, eighth_mul, one_mul]

end NormalizedStructureTrace318
