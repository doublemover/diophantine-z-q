module
public import FramedLineInverse318
public import ModuleLocalGluing318
public import Mathlib.Tactic.Ring
public section
noncomputable section
namespace InverseLineSectionContraction318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace LineSheafClass318
open ModuleLocalGluing318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (L : Line X) (s : Γ(L.object,⊤))
local notation "I" => FramedLineInverse318.inverse L

abbrev coordinate (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :=
  (OpenLineFrameCoordinates318.frame L.object (L.opens i) (L.frame i) V h).symm
abbrev inverseCoordinate (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :=
  (OpenLineFrameCoordinates318.frame I.object (L.opens i) (I.frame i) V h).symm

lemma frame_transition {ι : Type u} (M : X.Modules) (U : ι → X.Opens)
    (e : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
    (i j : ι) (V : X.Opens) (hi : V≤U i) (hj : V≤U j) (t : Γ(M,V)) :
    (OpenLineFrameCoordinates318.frame M (U i) (e i) V hi).symm t =
    X.presheaf.map (homOfLE (le_inf hi hj)).op
      ((LineFrameCocycle318.cocycle M U e).transition i j).val *
      (OpenLineFrameCoordinates318.frame M (U j) (e j) V hj).symm t := by
  have h := LineFrameCocycle318.relation M U e i j V (le_inf hi hj)
    ((OpenLineFrameCoordinates318.frame M (U j) (e j) V hj).symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  apply (OpenLineFrameCoordinates318.frame M (U i) (e i) V hi).injective
  rw [LinearEquiv.apply_symm_apply]
  exact h.symm

/-- Literal local contraction using the original line frame and the
actual inverse transition-line frame on EVERY original subopen. -/
@[expose] def localMap (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :
    Γ(I.object,V) →ₗ[Γ(X,V)] Γ(X,V) where
  toFun t := inverseCoordinate L i V h t * coordinate L i V h
    (res L.object (show V≤⊤ from le_top) s)
  map_add' t u := by rw [map_add,add_mul]
  map_smul' a t := by rw [map_smul,smul_eq_mul,smul_eq_mul,mul_assoc]

lemma natural (i : L.Index) (V W : X.Opens) (hV : V≤L.opens i) (hW : W≤V)
    (t : Γ(I.object,V)) :
    X.presheaf.map (homOfLE hW).op (localMap L s i V hV t)=
      localMap L s i W (hW.trans hV) (res I.object hW t) := by
  change X.presheaf.map (homOfLE hW).op
    (inverseCoordinate L i V hV t * coordinate L i V hV (res L.object le_top s))=_
  rw [map_mul,OpenLineFrameCoordinates318.inverse_natural,
    OpenLineFrameCoordinates318.inverse_natural]
  rw [← Functor.map_comp_apply]
  rfl

lemma compatible (i j : L.Index) (V : X.Opens) (hi : V≤L.opens i) (hj : V≤L.opens j)
    (t : Γ(I.object,V)) : localMap L s i V hi t=localMap L s j V hj t := by
  have hI := frame_transition I.object L.opens I.frame i j V hi hj t
  have hL := frame_transition L.object L.opens L.frame i j V hi hj
    (res L.object (show V≤⊤ from le_top) s)
  have hu : (LineFrameCocycle318.cocycle I.object L.opens I.frame).transition i j =
      ((LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j)⁻¹ :=
    congrArg (fun z => z.transition i j)
      (LineSheafInverse318.original_inverse_transitions L.object L.opens L.frame)
  change inverseCoordinate L i V hi t * coordinate L i V hi (res L.object le_top s)=_
  rw [hI,hL,hu]
  let u := (LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j
  let r := X.presheaf.map (homOfLE (le_inf hi hj)).op
  have hz : r (u⁻¹).val * r u.val=1 := by rw [← map_mul,Units.inv_mul,map_one]
  calc
    (r (u⁻¹).val * inverseCoordinate L j V hj t) *
        (r u.val * coordinate L j V hj (res L.object le_top s)) =
        (r (u⁻¹).val * r u.val) *
          (inverseCoordinate L j V hj t * coordinate L j V hj (res L.object le_top s)) := by ring
    _ = localMap L s j V hj t := by rw [hz,one_mul]; rfl

/-- Compatible local maps on the FULL original overlap, not only generic
or pointwise agreement. -/
@[expose] def data : LocalData I.object (SheafOfModules.unit X.ringCatSheaf) L.opens where
  map := localMap L s
  natural := natural L s
  compatible := compatible L s

/-- A genuine global morphism from the actual inverse line into O_X.
Its construction uses original transition units and their checked inverses,
not an unsupported identification of inverse sheaf with a module dual. -/
@[expose] def hom : I.object ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ModuleLocalGluing318.hom (data L s) L.cover

lemma hom_on_subopen (i : L.Index) (V : X.Opens) (hV : V≤L.opens i)
    (t : Γ(I.object,V)) : (hom L s).app V t=localMap L s i V hV t := by
  have h := ModuleLocalGluing318.value_subopen (data L s) L.cover V V le_rfl i hV t
  simpa only [res_self] using h
/-- The image of the ACTUAL global inverse-line morphism on each framed
subopen is precisely the principal ideal of the original section coordinate.
This is an image equality, not equality of reduced supports. -/
lemma range_on_subopen (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) :
    LinearMap.range ((hom L s).val.app (op V)).hom =
      Ideal.span {coordinate L i V hV (res L.object (show V≤⊤ from le_top) s)} := by
  ext a
  constructor
  · rintro ⟨t,rfl⟩
    rw [hom_on_subopen L s i V hV]
    exact Ideal.mem_span_singleton'.mpr ⟨inverseCoordinate L i V hV t,rfl⟩
  · intro ha
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨(inverseCoordinate L i V hV).symm b,?_⟩
    rw [hom_on_subopen L s i V hV]
    change inverseCoordinate L i V hV ((inverseCoordinate L i V hV).symm b) *
      coordinate L i V hV (res L.object le_top s)=a
    rw [LinearEquiv.apply_symm_apply]
    exact hb

/-- On a regular frame, the ACTUAL inverse-line morphism is injective,
with the same coordinate used by its proven literal ideal image. -/
lemma injective_on_subopen (i : L.Index) (V : X.Opens) (hV : V≤L.opens i)
    (hr : ∀ a : Γ(X,V),a * coordinate L i V hV
      (res L.object (show V≤⊤ from le_top) s)=0 → a=0) :
    Function.Injective ((hom L s).app V) := by
  intro t u h
  apply (inverseCoordinate L i V hV).injective
  apply sub_eq_zero.mp
  apply hr
  rw [sub_mul]
  exact sub_eq_zero.mpr (by
    rw [hom_on_subopen L s i V hV,hom_on_subopen L s i V hV] at h
    exact h)
end InverseLineSectionContraction318
