module
public import PELOriginalContactRootDeck318
public import FourRootCoordinateRingSigns318
public section
noncomputable section
namespace PELOriginalRegularCoordinateAlgebra318
open PELOriginalContactRootFunctions318 PELOriginalCommonContactBase318
open PELOriginalMaximalQuotient318
abbrev OriginalRegular := RegularSource
abbrev Functions := OriginalRegular → ℂ
abbrev CoordinateRing := FourRootAffineCoordinateRing318.Ring branches

@[expose] def originalBase : Functions := fun x => base x.val
@[expose] def originalRoot (k : Fin 4) : Functions := fun x => roots x.val k
lemma original_relation (k : Fin 4) :
    originalRoot k ^ 2 = originalBase - algebraMap ℂ Functions (branches k) := by
  funext x
  exact roots_square x.val x.property k

/-- Evaluation into genuine functions on the entire original regular
source, built from its independently constructed base and roots. This is
not defined via a model scheme or by transporting a function field. -/
@[expose] def evaluation : CoordinateRing →ₐ[ℂ] Functions :=
  FourRootAffineCoordinateRing318.lift branches originalBase originalRoot original_relation
lemma evaluation_base :
    evaluation (FourRootAffineCoordinateRing318.coordinate branches none) = originalBase :=
  FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _
lemma evaluation_root (k : Fin 4) :
    evaluation (FourRootAffineCoordinateRing318.coordinate branches (some k)) = originalRoot k :=
  FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _

/-- Literal evaluation at an old point, retaining the complex scalar map. -/
@[expose] def atPoint (x : OriginalRegular) : CoordinateRing →ₐ[ℂ] ℂ where
  toFun a := evaluation a x
  map_zero' := congrFun (map_zero evaluation) x
  map_one' := congrFun (map_one evaluation) x
  map_add' a b := congrFun (map_add evaluation a b) x
  map_mul' a b := congrFun (map_mul evaluation a b) x
  commutes' c := congrFun (evaluation.commutes c) x
lemma atPoint_base (x : OriginalRegular) :
    atPoint x (FourRootAffineCoordinateRing318.coordinate branches none) = base x.val :=
  congrFun evaluation_base x
lemma atPoint_root (x : OriginalRegular) (k : Fin 4) :
    atPoint x (FourRootAffineCoordinateRing318.coordinate branches (some k)) = roots x.val k :=
  congrFun (evaluation_root k) x

/-- The actual coordinate algebra separates ALL original regular points,
including different fibers. This is not injectivity of evaluation as an
algebra map, which is a separate missing producer. -/
theorem separates (x y : OriginalRegular)
    (h : ∀ a : CoordinateRing, evaluation a x = evaluation a y) : x = y := by
  apply Subtype.ext
  apply base_roots_injective x.val y.val x.property y.property
  · simpa only [evaluation_base] using h (FourRootAffineCoordinateRing318.coordinate branches none)
  · intro k
    simpa only [evaluation_root] using h (FourRootAffineCoordinateRing318.coordinate branches (some k))

/-- Every complex algebra point over every regular base value is exactly
realized by an old point, on the WHOLE coordinate ring, not just its five
generators. No algebraic point outside the regular domain is claimed here. -/
theorem every_regular_algebra_point (f : CoordinateRing →ₐ[ℂ] ℂ)
    (hf : FourCharacterRootRecombination318.denominator branches
      (f (FourRootAffineCoordinateRing318.coordinate branches none)) ≠ 0) :
    ∃ x : OriginalRegular, atPoint x = f := by
  let q := FourRootAffineCoordinateRing318.point branches f
  obtain ⟨x,hx,hbase,hroots⟩ := all_roots q.val.1 hf q.val.2 q.property
  refine ⟨⟨x,hx⟩,?_⟩
  apply FourRootAffineCoordinateRing318.hom_ext
  intro k
  cases k with
  | none => exact (atPoint_base ⟨x,hx⟩).trans hbase
  | some k => exact (atPoint_root ⟨x,hx⟩ k).trans (hroots k)

@[expose] def originalAction (w : Labels) (x : OriginalRegular) : OriginalRegular :=
  ⟨w • x.val,PELOriginalContactRootDeck318.original_regular w x.val x.property⟩

/-- Exact full-ring equivariance against the original arithmetic labels.
The finite/root formulas are promoted by the literal coordinate-ring
universal property, without an arbitrary transported action. -/
theorem deck_evaluation (w : Labels) (x : OriginalRegular) :
    atPoint (originalAction w x) = (atPoint x).comp
      (FourRootCoordinateRingSigns318.finiteEnd branches (OriginalContactInertiaBasis318.basis w)) := by
  apply FourRootAffineCoordinateRing318.hom_ext
  intro k
  cases k with
  | none =>
      simp only [AlgHom.comp_apply,FourRootCoordinateRingSigns318.finite_base,atPoint_base]
      exact PELOriginalContactRootDeck318.base_action w x.val
  | some k =>
      simp only [AlgHom.comp_apply,FourRootCoordinateRingSigns318.finite_root,
        map_mul,AlgHom.commutes,Algebra.algebraMap_self_apply,atPoint_root]
      exact PELOriginalContactRootDeck318.roots_action w x.val x.property k
end PELOriginalRegularCoordinateAlgebra318
