module
public import LineSheafTensorIsos318
public import FramedLineInverse318
public section
noncomputable section
namespace IntrinsicLineDifference318
open AlgebraicGeometry CategoryTheory
open LineSheafClass318
universe u
variable {X : Scheme.{u}} (M N : X.Modules) {ι : Type u}
  (U : ι → X.Opens) (hc : (⊤ : X.Opens) ≤ ⨆ i,U i)
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)

/-- The actual numerator line, retaining its full original chart frames. -/
@[expose] def numerator : Line X := ⟨M,ι,U,hc,em⟩
@[expose] def denominator : Line X := ⟨N,ι,U,hc,en⟩

/-- A genuine sheafified tensor with the actual inverse cocycle SHEAF.
This is not a formal difference of line labels or an assumed cube root. -/
@[expose] def object : X.Modules :=
  IntrinsicTensorSheaf318.tensor M (LineSheafInverse318.object N U en)

/-- Actual unit frames on the unchanged common cover. -/
@[expose] def frames (i : ι) : SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅
    (object M N U en).restrict (U i).ι :=
  TensorLineLocalFrame318.frame M (LineSheafInverse318.object N U en) (U i)
    (em i) (LineSheafInverse318.frame N U en i)

@[expose] def line : Line X := ⟨object M N U en,ι,U,hc,frames M N U em en⟩

include hc em in
/-- Bundled local freeness is produced from actual single-generator
frames on the full covering family. -/
lemma locallyFree : (object M N U en).IsLocallyFree :=
  ModuleFreeOpenFrames318.locallyFree (object M N U en) PUnit.{u+1} U hc
    (fun i => CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u+1} => SheafOfModules.unit (U i).toScheme.ringCatSheaf) ≪≫
      frames M N U em en i)

/-- Exact equality of WHOLE regular transition-unit cocycles, on every
full scheme intersection. Numerator times inverse denominator retains
the original sheaf frame normalization. -/
theorem cocycle_eq :
    LineFrameCocycle318.cocycle (object M N U en) U (frames M N U em en) =
      UnitCocycleProduct318.product (LineFrameCocycle318.cocycle M U em)
        (UnitCocycleInverse318.inverse (LineFrameCocycle318.cocycle N U en)) := by
  change LineFrameCocycle318.cocycle
    (IntrinsicTensorSheaf318.tensor M (LineSheafInverse318.object N U en)) U
    (TensorLineCocycle318.frames M (LineSheafInverse318.object N U en) U em
      (LineSheafInverse318.frame N U en)) = _
  rw [TensorLineCocycle318.cocycle_eq,LineSheafInverse318.original_inverse_transitions]

/-- The literal quotient transition unit, before evaluating at ANY point. -/
theorem transition (i j : ι) :
    (LineFrameCocycle318.cocycle (object M N U en) U (frames M N U em en)).transition i j =
      (LineFrameCocycle318.cocycle M U em).transition i j *
        ((LineFrameCocycle318.cocycle N U en).transition i j)⁻¹ := by
  rw [cocycle_eq]
  rfl

/-- Actual tensor cancellation restores the unchanged numerator module
sheaf, with genuine categorical inverse maps. -/
@[expose] def cancellation :
    IntrinsicTensorSheaf318.tensor (object M N U en) N ≅ M :=
  LineSheafTensorIsos318.assoc (numerator M U hc em)
    (FramedLineInverse318.inverse (denominator N U hc en)) (denominator N U hc en) ≪≫
  TensorSheafFunctor318.congr (Iso.refl M)
    (FramedLineInverse318.leftIso (denominator N U hc en)) ≪≫
  LineSheafTensorIsos318.rightUnit (numerator M U hc em)

lemma cancellation_hom_inv :
    (cancellation M N U hc em en).hom ≫ (cancellation M N U hc em en).inv = 𝟙 _ :=
  (cancellation M N U hc em en).hom_inv_id

lemma cancellation_inv_hom :
    (cancellation M N U hc em en).inv ≫ (cancellation M N U hc em en).hom = 𝟙 _ :=
  (cancellation M N U hc em en).inv_hom_id

/-- Exact unit-valued specialization of the actual algebraic transition,
valid for ANY coefficient-ring homomorphism, not only chosen points. -/
theorem transition_map (i j : ι) {A : Type u} [CommRing A]
    (f : Γ(X,U i ⊓ U j) →+* A) :
    Units.map f.toMonoidHom
      ((LineFrameCocycle318.cocycle (object M N U en) U (frames M N U em en)).transition i j) =
    Units.map f.toMonoidHom ((LineFrameCocycle318.cocycle M U em).transition i j) *
      (Units.map f.toMonoidHom ((LineFrameCocycle318.cocycle N U en).transition i j))⁻¹ := by
  rw [transition,map_mul,map_inv]
end IntrinsicLineDifference318
