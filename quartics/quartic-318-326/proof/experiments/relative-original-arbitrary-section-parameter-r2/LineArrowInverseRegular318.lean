module
public import LineArrowInverseSection318
public section
noncomputable section
namespace LineArrowInverseRegular318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open LineArrowInverseLocal318
universe u
variable {X : Scheme.{u}} (L : Line X) (f : L.object ⟶ SheafOfModules.unit X.ringCatSheaf)

lemma apply_frame (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) (a : Γ(X,V)) :
    f.app V (frame L i V hV a)=a*coefficient L f i V hV := by
  calc
    _ = f.app V (a • frame L i V hV 1) := by
      congr 1
      rw [← (frame L i V hV).map_smul,smul_eq_mul,mul_one]
    _ = _ := (f.val.app (op V)).hom.map_smul a _

lemma image (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) :
    LinearMap.range (f.val.app (op V)).hom=Ideal.span {coefficient L f i V hV} := by
  ext a
  constructor
  · rintro ⟨t,rfl⟩
    refine Ideal.mem_span_singleton'.mpr ⟨(frame L i V hV).symm t,?_⟩
    exact (apply_frame L f i V hV _).symm.trans
      (congrArg (fun t => f.app V t) ((frame L i V hV).apply_symm_apply t))
  · intro ha
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨frame L i V hV b,(apply_frame L f i V hV b).trans hb⟩

/-- An actual MONO line inclusion gives a nonzerodivisor coefficient;
this is section injectivity of the genuine sheaf map, not support data. -/
lemma regular [Mono f] (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) :
    ∀ a : Γ(X,V),a*coefficient L f i V hV=0 → a=0 := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op V)
  haveI : Mono (E.map f) := inferInstance
  have hi : Function.Injective (f.app V) :=
    (ModuleCat.mono_iff_injective (E.map f)).mp inferInstance
  intro a ha
  have hz : frame L i V hV a=0 := hi (by rw [apply_frame,ha,map_zero])
  exact (frame L i V hV).injective (hz.trans (map_zero _).symm)
end LineArrowInverseRegular318
