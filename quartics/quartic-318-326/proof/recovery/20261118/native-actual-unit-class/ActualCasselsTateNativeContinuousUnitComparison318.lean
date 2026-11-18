module
public import ActualCasselsTateNativeContinuousCycleClass318
public import ActualCasselsTateContinuousThirdObstruction318
public import ActualTwoDescentPrimaryCocycleUniformLevel318
import all ActualCasselsTateUnitCoefficients318
import all ActualCasselsTateUnitCohomology318
import all ActualCasselsTateContinuousUnitDifferential318
public section
noncomputable section
namespace ActualCasselsTateNativeContinuousUnitComparison318
open ActualCasselsTateUnitCoefficients318 ActualCasselsTateUnitCohomology318
open ActualCasselsTateContinuousUnitDifferential318 ActualCasselsTateContinuousThirdObstruction318
open ActualCasselsTateNativeContinuousCycleClass318
open ActualTwoDescentFieldContinuousGaloisCocycles318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Gal" => Field.absoluteGaloisGroup F
local notation "U" => (AlgebraicClosure F)ˣ
local notation "A" => Additive U
local instance : TopologicalSpace A := ⊥
local instance : DiscreteTopology A := discreteTopology_bot A

/-- Actual Krull group, actual representation on all closure units; the
discrete topology is on the coefficients only. -/
def topUnitRepresentation : ContRepresentation ℤ Gal A :=
  .ofMonoidHom {
    toFun := fun σ => ⟨(unitRepresentation (F:=F)) σ, continuous_of_discreteTopology⟩
    map_one' := by
      apply ContinuousLinearMap.ext
      intro u
      exact congrArg Additive.ofMul (unitAction_one u.toMul)
    map_mul' := by
      intro σ τ
      apply ContinuousLinearMap.ext
      intro u
      exact congrArg Additive.ofMul (unitAction_mul σ τ u.toMul) }

def topUnits : TopRep ℤ Gal := TopRep.of (topUnitRepresentation (F:=F))

lemma actualAction_continuous :
    Continuous (fun p : Gal × (topUnits (F:=F)) => (topUnits (F:=F)).ρ p.1 p.2) := by
  have h := unitAction_family_locally_constant (fun u : A => u.toMul)
    (IsLocallyConstant.of_discrete _)
  exact (h.comp (Additive.ofMul : U → A)).continuous

def nativeUnitCoordinates (z : continuousUnitThreeCocycles (F:=F)) :
    C(Gal × Gal × Gal,topUnits (F:=F)) :=
  ⟨fun g => Additive.ofMul (z g),(z.property.1.comp (Additive.ofMul : U → A)).continuous⟩

lemma nativeUnitCoordinates_closed (z : continuousUnitThreeCocycles (F:=F)) :
    closedThree (topUnits (F:=F)) (nativeUnitCoordinates z) := by
  intro g h l m
  exact (ofMul_unitDThree (fun a b c => z (a,b,c)) g h l m).symm.trans
    (congrArg Additive.ofMul (z.property.2 g h l m))

def nativeUnitThreeClass (z : continuousUnitThreeCocycles (F:=F)) :
    continuousCohomology 3 (topUnits (F:=F)) :=
  nativeThreeClass _ actualAction_continuous _ (nativeUnitCoordinates_closed z)

/-- Same representative on both sides; an equality of vanishing criteria
in the native continuous complex and the concrete locally constant quotient.
No global or local arithmetic vanishing theorem enters this comparison. -/
theorem nativeUnitThreeClass_eq_zero_iff (z : continuousUnitThreeCocycles (F:=F)) :
    nativeUnitThreeClass z = 0 ↔ (QuotientGroup.mk z : ContinuousUnitHThree (F:=F)) = 1 := by
  unfold nativeUnitThreeClass
  rw [nativeThreeClass_zero_iff,QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨b,hb⟩
    have hb' : IsLocallyConstant (fun p : Gal × Gal => (b p : A)) :=
      (IsLocallyConstant.iff_continuous _).mpr b.continuous
    let bm : continuousUnitTwo (F:=F) := ⟨fun p => (b p : A).toMul,hb'.comp Additive.toMul⟩
    refine ⟨bm,?_⟩
    apply Subtype.ext
    funext p
    rcases p with ⟨g,h,l⟩
    exact congrArg Additive.toMul
      ((ofMul_unitDTwo (fun a b' => bm (a,b')) g h l).trans (hb g h l))
  · rintro ⟨bm,hbm⟩
    let b : C(Gal × Gal,topUnits (F:=F)) :=
      ⟨fun p => Additive.ofMul (bm p),(bm.property.comp (Additive.ofMul : U → A)).continuous⟩
    refine ⟨b,?_⟩
    intro g h l
    have hv := congrArg (fun c : continuousUnitThreeCocycles (F:=F) => c (g,h,l)) hbm
    exact (ofMul_unitDTwo (fun a b' => bm (a,b')) g h l).symm.trans
      (congrArg Additive.ofMul hv)

/-- The earlier concrete obstruction is the right hand side for exactly the
project defect, with no replacement of the input by a cohomologous cycle. -/
theorem nativeDefect_eq_zero_iff (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    nativeUnitThreeClass (continuousDefect n hn χ ψ) = 0 ↔
      actualThirdObstruction n hn χ ψ = 1 :=
  nativeUnitThreeClass_eq_zero_iff _
end ActualCasselsTateNativeContinuousUnitComparison318
