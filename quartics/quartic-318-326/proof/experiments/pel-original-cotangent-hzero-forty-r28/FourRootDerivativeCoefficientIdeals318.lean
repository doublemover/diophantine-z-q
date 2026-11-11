module
public import FourRootDerivativeGeneratorUnits318
public import FourRootDerivativeTestSections318
public import LocalPulledGeneratorUnit318
public import FramedMorphismCoefficientAssociates318
public section
noncomputable section
namespace FourRootDerivativeCoefficientIdeals318
open AlgebraicGeometry CategoryTheory Opposite
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootActualCanonicalLine318 FourRootDerivativeFramedLines318
open FourRootProjectiveDifferential318 FourRootProjectiveDifferentialCharts318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
@[expose] def baseGenerator(i:Option (Fin 4)):Γ(baseOmega,baseOpen b i):=by
  cases i with
  | none=>simpa only [baseOpen,Scheme.Hom.image_top_eq_opensRange] using infinityBaseGenerator b
  | some i=>simpa only [baseOpen,Scheme.Hom.image_top_eq_opensRange] using finiteBaseGenerator
lemma base_unit(i:Option (Fin 4)):
    IsUnit ((OpenLineFrameCoordinates318.frame baseOmega (baseOpen b i)
      (baseFrame b i) (baseOpen b i) le_rfl).symm (baseGenerator b i)):=by
  cases i with
  | none=>
    have h:baseOpen b none≤infinityBaseChart b ''ᵁ ⊤:=by
      simp only [baseOpen,Scheme.Hom.image_top_eq_opensRange,le_refl]
    have hh:=FourRootDerivativeGeneratorUnits318.infinity_base_unit b (baseOpen b none) h
      (OpenLineFrameCoordinates318.frame baseOmega (baseOpen b none) (baseFrame b none) _ le_rfl)
    simpa only [baseGenerator,baseOpen,Scheme.Hom.image_top_eq_opensRange,
      homOfLE_refl,op_id,Functor.map_id] using hh
  | some i=>
    have h:baseOpen b (some i)≤finiteBaseChart ''ᵁ ⊤:=by
      simp only [baseOpen,Scheme.Hom.image_top_eq_opensRange,le_refl]
    have hh:=FourRootDerivativeGeneratorUnits318.finite_base_unit (baseOpen b (some i)) h
      (OpenLineFrameCoordinates318.frame baseOmega (baseOpen b (some i)) (baseFrame b (some i)) _ le_rfl)
    simpa only [baseGenerator,baseOpen,Scheme.Hom.image_top_eq_opensRange,
      homOfLE_refl,op_id,Functor.map_id] using hh

variable (i:Option (Fin 4))(V:(scheme b).Opens)(h:V≤opens b hb i)
@[expose] def sourceTest:Γ(sourceObject b,V):=
  (sourceObject b).presheaf.map (homOfLE (h.trans (source_open_le b hb i))).op
    (LocalPullbackUnit318.pull (FourRootProjectiveProjection318.projection b) baseOmega
      (baseOpen b i) (baseGenerator b i))
@[expose] def targetTest:Γ(omega b,V):=by
  cases i with
  | none=>exact (omega b).presheaf.map (homOfLE (show V≤infinityEmbedding b hb ''ᵁ ⊤ from by
      simpa only [opens,FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange] using h)).op
        (infinityGenerator b hb)
  | some j=>exact (omega b).presheaf.map (homOfLE (show V≤finiteEmbedding b j ''ᵁ ⊤ from by
      simpa only [opens,FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange] using h)).op
        (finiteGenerator b j)
/-- The literal derivative coefficient in the ORIGINAL root charts.
Infinity is the derivative of v=u², not the pole coefficient of dt. -/
@[expose] def literal:Γ(scheme b,V):=by
  cases i with
  | none=>exact (scheme b).presheaf.map (homOfLE (show V≤infinityEmbedding b hb ''ᵁ ⊤ from by
      simpa only [opens,FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange] using h)).op
        (((infinityEmbedding b hb).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (InfinityRing b hb))).inv
            (2*FourRootActualInfinityKaehler318.coordinate b hb)))
  | some j=>exact (scheme b).presheaf.map (homOfLE (show V≤finiteEmbedding b j ''ᵁ ⊤ from by
      simpa only [opens,FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange] using h)).op
        (((finiteEmbedding b j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b j))).inv
            (2*FourRootActualBranchKaehler318.sourceCoordinate b j)))

lemma source_unit:
    IsUnit ((OpenLineFrameCoordinates318.frame (sourceObject b) (opens b hb i)
      (sourceFrame b hb i) V h).symm (sourceTest b hb i V h)):=by
  rw [sourceFrame,OpenLineFrameRefinement318.coordinates]
  exact LocalPulledGeneratorUnit318.subopen (FourRootProjectiveProjection318.projection b)
    baseOmega (baseOpen b i) (baseFrame b i) (baseGenerator b i) (base_unit b i)
      V (h.trans (source_open_le b hb i))
lemma target_unit:
    IsUnit ((OpenLineFrameCoordinates318.frame (omega b) (opens b hb i)
      (frame b hb i) V h).symm (targetTest b hb i V h)):=by
  cases i with
  | none=>exact FourRootActualIntrinsicFrameComparison318.infinity_generator_unit b hb V
      (OpenLineFrameCoordinates318.frame (omega b) (opens b hb none) (frame b hb none) V h)
      (by simpa only [opens,FourRootWholeCanonicalCover318.embedding,
        Scheme.Hom.image_top_eq_opensRange] using h)
  | some j=>exact FourRootActualIntrinsicFrameComparison318.finite_generator_unit b V
      (OpenLineFrameCoordinates318.frame (omega b) (opens b hb (some j)) (frame b hb (some j)) V h)
      j (by simpa only [opens,FourRootWholeCanonicalCover318.embedding,
        Scheme.Hom.image_top_eq_opensRange] using h)
/-- The SAME original universal derivative acts on these actual local
source generators by the literal chart equation on the WHOLE V. -/
lemma image:
    (actualDerivative b hb).app V (sourceTest b hb i V h)=
      literal b hb i V h • targetTest b hb i V h:=by
  cases i with
  | none=>
    have hV:V≤infinityEmbedding b hb ''ᵁ ⊤:=by
      simpa only [opens,FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange] using h
    have hh:=PresheafOfModules.naturality_apply (derivative b).val (homOfLE hV).op
      (FourRootDerivativeTestSections318.infinitySource b hb)
    rw [FourRootDerivativeTestSections318.infinity_image,(omega b).val.map_smul] at hh
    simpa only [sourceTest,sourceObject,actualDerivative,baseGenerator,baseOpen,
      FourRootDerivativeTestSections318.infinitySource,targetTest,literal,
      ←Functor.map_comp_apply,←op_comp,homOfLE_comp,Scheme.Hom.image_top_eq_opensRange] using hh
  | some j=>
    have hV:V≤finiteEmbedding b j ''ᵁ ⊤:=by
      simpa only [opens,FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange] using h
    have hh:=PresheafOfModules.naturality_apply (derivative b).val (homOfLE hV).op
      (FourRootDerivativeTestSections318.finiteSource b j)
    rw [FourRootDerivativeTestSections318.finite_image,(omega b).val.map_smul] at hh
    simpa only [sourceTest,sourceObject,actualDerivative,baseGenerator,baseOpen,
      FourRootDerivativeTestSections318.finiteSource,targetTest,literal,
      ←Functor.map_comp_apply,←op_comp,homOfLE_comp,Scheme.Hom.image_top_eq_opensRange] using hh
/-- Extracted coefficient of the ACTUAL derivative equals the literal
2z_i/2u coefficient times a derived REGULAR UNIT. This closes the actual
frame-normalization gate, rather than guessing a scalar convention. -/
theorem unit_multiple:
    ∃u:Γ(scheme b,V)ˣ,FourRootDerivativeContraction318.coefficient b hb i V h=
      u.val*literal b hb i V h:=
  FramedMorphismCoefficientAssociates318.unit_multiple
    (OpenLineFrameCoordinates318.frame (sourceObject b) (opens b hb i) (sourceFrame b hb i) V h)
    (OpenLineFrameCoordinates318.frame (omega b) (opens b hb i) (frame b hb i) V h)
    ((actualDerivative b hb).val.app (op V)).hom
    (sourceTest b hb i V h) (targetTest b hb i V h) (literal b hb i V h)
    (image b hb i V h) (source_unit b hb i V h) (target_unit b hb i V h)
/-- Exact principal image ideals on every subordinate open, with full
multiplicity retained. No generic-field, support or radical shortcut. -/
theorem coefficient_ideal:
    Ideal.span {FourRootDerivativeContraction318.coefficient b hb i V h}=
      Ideal.span {literal b hb i V h}:=
  FramedMorphismCoefficientAssociates318.span_eq
    (OpenLineFrameCoordinates318.frame (sourceObject b) (opens b hb i) (sourceFrame b hb i) V h)
    (OpenLineFrameCoordinates318.frame (omega b) (opens b hb i) (frame b hb i) V h)
    ((actualDerivative b hb).val.app (op V)).hom
    (sourceTest b hb i V h) (targetTest b hb i V h) (literal b hb i V h)
    (image b hb i V h) (source_unit b hb i V h) (target_unit b hb i V h)
end FourRootDerivativeCoefficientIdeals318
