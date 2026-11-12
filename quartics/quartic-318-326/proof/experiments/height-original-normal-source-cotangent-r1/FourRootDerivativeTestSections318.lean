module
public import FourRootDerivativeContraction318
public import LocalPullbackUnit318
public section
noncomputable section
namespace FourRootDerivativeTestSections318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootProjectiveProjection318
open FourRootIntrinsicCanonicalFrames318 FourRootProjectiveDifferential318
open FourRootProjectiveDifferentialCharts318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
/-- The actual local source section is the ORIGINAL base generator
pulled by the real adjunction unit, then restricted to the real chart.
No desired derivative coefficient enters its construction. -/
@[expose] def finiteSource(i:Fin 4):
    Γ((Scheme.Modules.pullback (projection b)).obj baseOmega,finiteEmbedding b i ''ᵁ ⊤):=
  ((Scheme.Modules.pullback (projection b)).obj baseOmega).presheaf.map
    (homOfLE (finite_preimage b i)).op
      (LocalPullbackUnit318.pull (projection b) baseOmega
        (finiteBaseChart ''ᵁ ⊤) finiteBaseGenerator)
@[expose] def infinitySource:
    Γ((Scheme.Modules.pullback (projection b)).obj baseOmega,infinityEmbedding b hb ''ᵁ ⊤):=
  ((Scheme.Modules.pullback (projection b)).obj baseOmega).presheaf.map
    (homOfLE (infinity_preimage b hb)).op
      (LocalPullbackUnit318.pull (projection b) baseOmega
        (infinityBaseChart b ''ᵁ ⊤) (infinityBaseGenerator b))
/-- Exact action of the SAME genuine pullback derivative on the actual
pulled finite generator. The coefficient 2z_i is inherited from the
independently proved universal differential equation. -/
theorem finite_image(i:Fin 4):
    (derivative b).app (finiteEmbedding b i ''ᵁ ⊤) (finiteSource b i)=
      ((finiteEmbedding b i).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
          (2*FourRootActualBranchKaehler318.sourceCoordinate b i)) • finiteGenerator b i:=by
  have h:=LocalPullbackUnit318.adjoint_subopen (projection b) (derivative b)
    (finiteBaseChart ''ᵁ ⊤) (finiteEmbedding b i ''ᵁ ⊤)
    (finite_preimage b i) finiteBaseGenerator
  rw [derivative_adjoint] at h
  change (derivative b).app _ (finiteSource b i)=finiteValue b i finiteBaseGenerator at h
  exact h.trans (finite_generator_image b i)
/-- Infinity keeps the genuine translated base differential dv,
whose image is 2u du. The meromorphic coefficient of dt is unrelated
to this local base frame and is not substituted here. -/
theorem infinity_image:
    (derivative b).app (infinityEmbedding b hb ''ᵁ ⊤) (infinitySource b hb)=
      ((infinityEmbedding b hb).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (InfinityRing b hb))).inv
          (2*FourRootActualInfinityKaehler318.coordinate b hb)) • infinityGenerator b hb:=by
  have h:=LocalPullbackUnit318.adjoint_subopen (projection b) (derivative b)
    (infinityBaseChart b ''ᵁ ⊤) (infinityEmbedding b hb ''ᵁ ⊤)
    (infinity_preimage b hb) (infinityBaseGenerator b)
  rw [derivative_adjoint] at h
  change (derivative b).app _ (infinitySource b hb)=infinityValue b hb (infinityBaseGenerator b) at h
  exact h.trans (infinity_generator_image b hb)
end FourRootDerivativeTestSections318
