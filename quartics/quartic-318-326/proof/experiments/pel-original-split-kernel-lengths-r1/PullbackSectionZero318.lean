module
public import ModuleOpenZeroDetection318
public import SectionFrameMorphismFormula318
public import PullbackChartNaturality318
public import PullbackScalar318
public import OpenPointScalarPullback318
public section
noncomputable section
namespace PullbackSectionZero318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}
lemma multiply_zero_iff (a : Γ(X,⊤)) : ClutchedModule318.multiply a=0 ↔ a=0 := by
  constructor
  · intro h
    have he := congrArg (fun φ => φ.app ⊤ (1 : Γ(X,⊤))) h
    simpa only [ClutchedModule318.multiply_top,one_mul,zero_apply] using he
  · intro h
    apply ModuleTopExt318.ext
    simp only [ClutchedModule318.multiply_top,h,mul_zero,zero_apply]
lemma pullback_multiply_zero_iff (f : X ⟶ Y) (a : Γ(Y,⊤)) :
    (Scheme.Modules.pullback f).map (ClutchedModule318.multiply a)=0 ↔ f.appTop a=0 := by
  rw [←multiply_zero_iff (f.appTop a)]
  constructor
  · intro h
    apply (cancel_epi (IdentityCotangent318.pullbackUnitIso f).hom).1
    rw [←PullbackScalar318.pullback_multiply,h,zero_comp,comp_zero]
  · intro h
    apply (cancel_mono (IdentityCotangent318.pullbackUnitIso f).hom).1
    rw [PullbackScalar318.pullback_multiply,h,comp_zero,zero_comp]

variable (f : X ⟶ Y) (M : Y.Modules)
  (σ : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (U : Y.Opens)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
  (c : Γ(Y,U))
  (hc : ∀ (W : Y.Opens) (hW : W≤U),σ.app W 1=
    OpenLineFrameCoordinates318.frame M U e W hW (Y.presheaf.map (homOfLE hW).op c))

/-- Exact zero comparison under the natural change-of-chart iso. No
flatness is used: only the actual pullback and restriction functors. -/
lemma chart_zero_iff :
    (Scheme.Modules.restrictFunctor (f⁻¹ᵁU).ι).map ((Scheme.Modules.pullback f).map σ)=0 ↔
      (Scheme.Modules.pullback (LinePullbackFrames318.chartMap f U)).map
        ((Scheme.Modules.restrictFunctor U.ι).map σ)=0 := by
  let α := PullbackChartNaturality318.chartNatIso f U.ι (f⁻¹ᵁU).ι
    (LinePullbackFrames318.chartMap f U) (LinePullbackFrames318.square f U)
  have hn := α.hom.naturality σ
  simp only [Functor.comp_map] at hn
  constructor
  · intro h
    apply (cancel_epi (α.hom.app (SheafOfModules.unit Y.ringCatSheaf))).1
    rw [←hn,h,zero_comp,comp_zero]
  · intro h
    apply (cancel_mono (α.hom.app M)).1
    rw [hn,h,comp_zero,zero_comp]
include hc in
lemma local_zero_iff :
    (Scheme.Modules.restrictFunctor (f⁻¹ᵁU).ι).map ((Scheme.Modules.pullback f).map σ)=0 ↔
      f.app U c=0 := by
  rw [chart_zero_iff]
  let g := LinePullbackFrames318.chartMap f U
  let r := (LineFrameTopScalar318.ringTop U).inv c
  have hφ := SectionFrameMorphismFormula318.restriction_formula M U e σ c hc
  rw [hφ,Functor.map_comp,Functor.map_comp]
  have hmul : ((Scheme.Modules.pullback g).map (Scheme.Modules.restrictUnitIso U.ι).hom≫
      (Scheme.Modules.pullback g).map (ClutchedModule318.multiply r)≫
      (Scheme.Modules.pullback g).map e.hom=0) ↔
      (Scheme.Modules.pullback g).map (ClutchedModule318.multiply r)=0 := by
    constructor
    · intro h
      apply (cancel_mono ((Scheme.Modules.pullback g).map e.hom)).1
      apply (cancel_epi ((Scheme.Modules.pullback g).map (Scheme.Modules.restrictUnitIso U.ι).hom)).1
      simpa only [Category.assoc,comp_zero,zero_comp] using h
    · intro h; rw [h,zero_comp,comp_zero]
  rw [hmul,pullback_multiply_zero_iff]
  change (f.resLE U (f⁻¹ᵁU) le_rfl).appTop ((LineFrameTopScalar318.ringTop U).inv c)=0 ↔ _
  rw [OpenPointScalarPullback318.restriction_square]
  constructor
  · intro h
    exact (LineFrameTopScalar318.ringTop (f⁻¹ᵁU)).inv.injective (h.trans (map_zero _).symm)
  · intro h; rw [h,map_zero]

/-- The true pulled-back SECTION MORPHISM vanishes exactly when all
literal pulled-back frame coefficients vanish in their entire rings. -/
theorem zero_iff {ι : Type u} (V : ι → Y.Opens) (hV : (⊤ : Y.Opens)≤⨆ i,V i)
    (frames : ∀ i,SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅ M.restrict (V i).ι)
    (coeff : ∀ i,Γ(Y,V i))
    (hcoeff : ∀ i (W : Y.Opens) (hW : W≤V i),σ.app W 1=
      OpenLineFrameCoordinates318.frame M (V i) (frames i) W hW
        (Y.presheaf.map (homOfLE hW).op (coeff i))) :
    (Scheme.Modules.pullback f).map σ=0 ↔ ∀ i,f.app (V i) (coeff i)=0 := by
  rw [ModuleOpenZeroDetection318.zero_iff _ (fun i => f⁻¹ᵁV i) (LinePullbackFrames318.preimage_cover f V hV)]
  exact forall_congr' (fun i => local_zero_iff f M σ (V i) (frames i) (coeff i) (hcoeff i))
end PullbackSectionZero318
