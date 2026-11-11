module
public import ActualIntrinsicFrameUnitComparison318
public import FourRootCanonicalRationalEquations318
public import ActualLineRationalEquationOrders318
public section
noncomputable section
namespace FourRootActualIntrinsicFrameComparison318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
variable (V:(scheme b).Opens)
    (e:Γ(scheme b,V)≃ₗ[Γ(scheme b,V)]Γ(omega b,V))
/-- The original signed-root generator remains a genuine generator on
every ambient subopen of its actual chart. Its coefficient in any other
actual ambient frame is therefore a REGULAR unit there. -/
theorem finite_generator_unit(i:Fin 4)(hV:V≤finiteEmbedding b i ''ᵁ ⊤):
    IsUnit (e.symm ((omega b).presheaf.map (homOfLE hV).op (finiteGenerator b i))):=
  ActualIntrinsicFrameUnitComparison318.original_generator_unit
    (finiteEmbedding b i) (structureMap b) (finite_structure b i)
    (FourRootActualBranchKaehler318.sourceFrame b i)
    (KaehlerDifferential.D ℂ (FiniteRing b i) (FourRootActualBranchKaehler318.sourceCoordinate b i))
    (FourRootActualBranchKaehler318.source_normalized b i) V hV e
/-- Exact actual intrinsic dt coefficient in ANY genuine ambient frame:
the literal restricted regular function 2z_i times the derived local
UNIT. No equality of separately transported frame is assumed. -/
theorem finite_dt_coefficient(i:Fin 4)(hV:V≤finiteEmbedding b i ''ᵁ ⊤):
    e.symm ((omega b).presheaf.map (homOfLE hV).op
      ((FamilyIntrinsicDifferentials318.D (structureMap b)).d
        (((finiteEmbedding b i).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
            (FourRootActualBranchKaehler318.sourceParameter b i)))))=
    (scheme b).presheaf.map (homOfLE hV).op
      (((finiteEmbedding b i).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
          (2*FourRootActualBranchKaehler318.sourceCoordinate b i))) *
      e.symm ((omega b).presheaf.map (homOfLE hV).op (finiteGenerator b i)):=by
  rw [finite_original_dt,(omega b).val.map_smul,map_smul,smul_eq_mul]

/-- At a genuine original Scheme DVR, the derived ambient frame unit
has order zero. Thus the actual intrinsic dt section has exactly the
valuation of its original literal regular coefficient 2z_i. -/
theorem finite_dt_value [IsIntegral (scheme b)] [Nonempty V]
    (x:scheme b)(hx:x∈V)[IsDiscreteValuationRing ((scheme b).presheaf.stalk x)]
    (i:Fin 4)(hV:V≤finiteEmbedding b i ''ᵁ ⊤):
    let ν:=ActualDvrMeromorphicOrder318.value ((scheme b).presheaf.stalk x) (scheme b).functionField
    ν ((scheme b).germToFunctionField V
      (e.symm ((omega b).presheaf.map (homOfLE hV).op
        ((FamilyIntrinsicDifferentials318.D (structureMap b)).d
          (((finiteEmbedding b i).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
              (FourRootActualBranchKaehler318.sourceParameter b i)))))))=
    ν ((scheme b).germToFunctionField V
      ((scheme b).presheaf.map (homOfLE hV).op
        (((finiteEmbedding b i).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
            (2*FourRootActualBranchKaehler318.sourceCoordinate b i))))):=by
  let ν:=ActualDvrMeromorphicOrder318.value ((scheme b).presheaf.stalk x) (scheme b).functionField
  let c:=e.symm ((omega b).presheaf.map (homOfLE hV).op (finiteGenerator b i))
  have hu:IsUnit ((scheme b).presheaf.germ V x hx c):=
    (finite_generator_unit b V e i hV).map ((scheme b).presheaf.germ V x hx).hom
  have hz:ν ((scheme b).germToFunctionField V c)=0:=by
    have h:=ActualDvrMeromorphicOrder318.value_unit ((scheme b).presheaf.stalk x)
      (scheme b).functionField _ hu
    rw [Scheme.algebraMap_germ_eq_germToFunctionField] at h
    exact h
  change ν _=ν _
  rw [finite_dt_coefficient,map_mul,ν.map_mul,hz,add_zero]

/-- The actual normalized u generator at every infinity chart has a
regular unit coefficient in any ambient frame on its genuine domain. -/
theorem infinity_generator_unit(hV:V≤infinityEmbedding b hb ''ᵁ ⊤):
    IsUnit (e.symm ((omega b).presheaf.map (homOfLE hV).op (infinityGenerator b hb))):=
  ActualIntrinsicFrameUnitComparison318.original_generator_unit
    (infinityEmbedding b hb) (structureMap b) (infinity_structure b hb)
    (FourRootActualInfinityKaehler318.frame b hb)
    (KaehlerDifferential.D ℂ (InfinityRing b hb) (FourRootActualInfinityKaehler318.coordinate b hb))
    (FourRootActualInfinityKaehler318.coordinate_normalized b hb) V hV e
/-- On the original infinity chart the pole-cleared canonical generator
is the ACTUAL section -2du; its coefficient is the SAME regular frame
unit times -2. The factor u^-3 is the separately proved original dt pole. -/
theorem infinity_cleared_coefficient(hV:V≤infinityEmbedding b hb ''ᵁ ⊤):
    e.symm ((-(2:Γ(scheme b,V))) •
      (omega b).presheaf.map (homOfLE hV).op (infinityGenerator b hb))=
    -(2:Γ(scheme b,V))*e.symm ((omega b).presheaf.map (homOfLE hV).op (infinityGenerator b hb)):=by
  rw [map_smul,smul_eq_mul]
end FourRootActualIntrinsicFrameComparison318
