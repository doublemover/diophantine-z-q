module
public import OpenClutchedGauge318
public import FifthNormLineTrivialization318
public section
noncomputable section
namespace FifthNormLineGauge318
open AlgebraicGeometry CategoryTheory Opposite
open FifthCompletedGlobal318 FifthNormClutchedLine318 FifthNormLineTrivialization318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma gauge_relation {G:Type*} [CommGroup G] (r₀ r₁ a b:G) (h:b=(r₀*r₁⁻¹)*a):r₁*b=a*r₀:=by
  rw [h,←mul_assoc,←mul_assoc r₁ r₀,mul_comm r₁ r₀,mul_assoc r₀ r₁,
    mul_inv_cancel,mul_one,mul_comm r₀ a]
variable (c d:FifthNormCocycle318.SourceCocycle cover)
  (s:∀i,SourceUnits.obj (op (cover i)))
  (hs:∀i j,d.transition i j=
    UnitTransitionCocycle318.coboundary SourceUnits cover s i j*c.transition i j)
include hs in
lemma compatible:
    Target.presheaf.map (homOfLE (show overlap≤right from inf_le_right)).op
        (coefficient s true).val*(targetTransition (d.transition false true)).val=
      (targetTransition (c.transition false true)).val*
        Target.presheaf.map (homOfLE (show overlap≤left from inf_le_left)).op
          (coefficient s false).val:=by
  let r₀:Γ(Target,overlap)ˣ:=Units.map
    (Target.presheaf.map (homOfLE (show overlap≤left from inf_le_left)).op).hom.toMonoidHom
    (coefficient s false)
  let r₁:Γ(Target,overlap)ˣ:=Units.map
    (Target.presheaf.map (homOfLE (show overlap≤right from inf_le_right)).op).hom.toMonoidHom
    (coefficient s true)
  have h:=congrArg (fun z=>FifthSheafNorm318.norm.hom.app (op overlap) z) (hs false true)
  rw [map_mul] at h
  change targetTransition (d.transition false true)=
    targetTransition (sourceCoboundary s)*targetTransition (c.transition false true) at h
  rw [target_coboundary] at h
  change targetTransition (d.transition false true)=
    (r₀*r₁⁻¹)*targetTransition (c.transition false true) at h
  exact congrArg Units.val (gauge_relation r₀ r₁ _ _ h)
/-- Explicit genuine normed line-sheaf isomorphism for the original specified
source change of frames. Its local multipliers are exactly their norms. -/
@[expose] def iso:lineOfCocycle c≅lineOfCocycle d:=
  OpenClutchedGauge318.iso left right (targetTransition (c.transition false true))
    (targetTransition (d.transition false true)) (coefficient s false) (coefficient s true)
    (compatible c d s hs)
/-- Gauge-equivalent specified source data yield isomorphic actual target
module sheaves. This is not a classification of arbitrary source line bundles. -/
lemma gaugeEquivalent (h:UnitTransitionCocycle318.GaugeEquivalent c d):
    Nonempty (lineOfCocycle c≅lineOfCocycle d):=by
  obtain ⟨s,hs⟩:=h
  exact ⟨iso c d s hs⟩
lemma pullback_line (c:FifthNormCocycle318.TargetCocycle cover):
    lineOfCocycle (FifthNormCocycle318.pullback c)=
      OpenClutchedLine318.line left right ((c.transition false true)^8):=by
  unfold lineOfCocycle normLine
  congr 1
  exact FifthNormCocycle318.pullback_transition c false true
end FifthNormLineGauge318
