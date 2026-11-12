module
public import FourRootCanonicalTransitionReconstruction318
public import ActualLineRationalEquations318
public import FourRootGluedFunctionField318
public import FourRootCanonicalMeromorphicBridge318
public section
noncomputable section
namespace FourRootCanonicalRationalEquations318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootWholeCanonicalCover318 FourRootActualCanonicalLine318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance integral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance affineDomain:IsDomain (FourRootAffineCoordinateRing318.Ring b):=
  FourRootActualGenericField318.affine_domain b hb
local instance infinityDomain:IsDomain (FourRootInfinityCoordinateRing318.Ring b):=
  FourRootInfinityDomain318.infinity_domain b hb
instance opens_nonempty(i:Option (Fin 4)):Nonempty (opens b hb i):=by
  have h:Nonempty (chart b hb i):=by
    cases i with
    | none=>
      letI:IsDomain (InfinityRing b hb):=Localization.Away.isDomain
        (FourRootActualMeromorphicInfinity318.denominator_ne b hb)
      exact inferInstance
    | some i=>
      letI:IsDomain (FiniteRing b i):=Localization.Away.isDomain
        (FourRootActualMeromorphicFinite318.denominator_ne b hb i)
      exact inferInstance
  obtain ⟨q⟩:=h
  exact ⟨⟨embedding b hb i q,⟨q,rfl⟩⟩⟩
instance overlap_nonempty(i j:Option (Fin 4)):
    Nonempty (opens b hb i⊓opens b hb j:(scheme b).Opens):=
  FunctionFieldGluing318.intersection_nonempty (scheme b) (opens b hb i) (opens b hb j)
lemma reference_open:finiteEmbedding b 0 ''ᵁ ⊤=opens b hb (some 0):=
  (finiteEmbedding b 0).image_top_eq_opensRange
/-- The ACTUAL intrinsic universal derivative on the reference chart. -/
@[expose] def originalReferenceSection:Γ(omega b,finiteEmbedding b 0 ''ᵁ ⊤):=
  (FamilyIntrinsicDifferentials318.D (structureMap b)).d
    (((finiteEmbedding b 0).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b 0))).inv
        (FourRootActualBranchKaehler318.sourceParameter b 0)))
/-- Only transport along equality of the SAME actual chart open. -/
@[expose] def referenceTransport:
    Γ(omega b,finiteEmbedding b 0 ''ᵁ ⊤)→+Γ(omega b,opens b hb (some 0)):=
  ((omega b).presheaf.mapIso (eqToIso (reference_open b hb).symm).op).hom.hom
lemma referenceTransport_injective:Function.Injective (referenceTransport b hb):=
  (ConcreteCategory.bijective_of_isIso
    ((omega b).presheaf.mapIso (eqToIso (reference_open b hb).symm).op).hom).injective
@[expose] def referenceSection:Γ(omega b,opens b hb (some 0)):=
  referenceTransport b hb (originalReferenceSection b)
/-- Its meromorphic realization is the SAME original dt already used
for the explicit DVR orders, by the universal differential comparison. -/
lemma reference_realized:
    FourRootCanonicalMeromorphicBridge318.finiteRealization b hb 0 (originalReferenceSection b)=
      KaehlerDifferential.D ℂ (FourRootActualMeromorphicFinite318.F b)
        (FourRootActualMeromorphicFinite318.t b):=
  FourRootCanonicalMeromorphicBridge318.original_dt_realized b hb 0
lemma originalReferenceSection_ne:originalReferenceSection b≠0:=by
  intro hz
  have hd:=reference_realized b hb
  rw [hz,map_zero] at hd
  have hc:=congrArg (FourRootActualMeromorphicFinite318.frame b hb 0) hd
  rw [map_zero,FourRootActualMeromorphicFinite318.dt_coefficient] at hc
  have hroot:FourRootActualMeromorphicFinite318.z b 0≠0:=
    (map_ne_zero_iff _ (IsFractionRing.injective (FourRootAffineCoordinateRing318.Ring b)
      (FourRootActualMeromorphicFinite318.F b))).mpr
      (FourRootActualLocalUniformizer318.source_root_ne_zero b hb 0)
  exact (mul_ne_zero (show (2:FourRootActualMeromorphicFinite318.F b)≠0 by norm_num) hroot) hc.symm
lemma referenceSection_ne:referenceSection b hb≠0:=by
  intro h
  apply originalReferenceSection_ne b hb
  apply referenceTransport_injective b hb
  exact h.trans (map_zero (referenceTransport b hb)).symm
/-- Anchor with the genuine ambient-frame coordinate of ORIGINAL
intrinsic dt itself. No compatibility between unrelated frame transports
is silently assumed. -/
@[expose] def referenceCoefficient:(scheme b).functionField:=
  (scheme b).germToFunctionField (opens b hb (some 0))
    ((OpenLineFrameCoordinates318.frame (omega b) (opens b hb (some 0))
      (frame b hb (some 0)) (opens b hb (some 0)) le_rfl).symm (referenceSection b hb))
lemma reference_nonzero:referenceCoefficient b hb≠0:=by
  intro h
  have hc:(OpenLineFrameCoordinates318.frame (omega b) (opens b hb (some 0))
      (frame b hb (some 0)) (opens b hb (some 0)) le_rfl).symm (referenceSection b hb)=0:=by
    apply (scheme b).germToFunctionField_injective (opens b hb (some 0))
    exact h.trans (map_zero _).symm
  apply referenceSection_ne b hb
  have he:=congrArg (OpenLineFrameCoordinates318.frame (omega b) (opens b hb (some 0))
    (frame b hb (some 0)) (opens b hb (some 0)) le_rfl) hc
  simpa only [LinearEquiv.apply_symm_apply,map_zero] using he
@[expose] def localEquation(i:Option (Fin 4)):(scheme b).functionField:=
  ActualLineRationalEquations318.equation (omega b) (opens b hb) (frame b hb)
    (some 0) (referenceCoefficient b hb) i
lemma localEquation_ne(i:Option (Fin 4)):localEquation b hb i≠0:=
  ActualLineRationalEquations318.equation_ne (omega b) (opens b hb) (frame b hb)
    (some 0) (referenceCoefficient b hb) (reference_nonzero b hb) i
lemma reference_equation:localEquation b hb (some 0)=referenceCoefficient b hb:=
  ActualLineRationalEquations318.equation_reference (omega b) (opens b hb) (frame b hb)
    (some 0) (referenceCoefficient b hb)
/-- The local rational equations have genuine regular-unit ratios on
EVERY complete overlap of the produced whole-Scheme canonical cover. -/
theorem actual_unit_ratio(i j:Option (Fin 4)):
    localEquation b hb i/localEquation b hb j=
      (scheme b).germToFunctionField (opens b hb i⊓opens b hb j)
        (LineFrameTransitions318.scalar (omega b) (opens b hb) (frame b hb) i j
          (opens b hb i⊓opens b hb j) inf_le_left inf_le_right).val:=
  ActualLineRationalEquations318.equation_ratio (omega b) (opens b hb) (frame b hb)
    (some 0) (referenceCoefficient b hb) (reference_nonzero b hb) i j
lemma reference_on_subopen(W:(scheme b).Opens)[Nonempty W]
    (h:W≤opens b hb (some 0)):
    (scheme b).germToFunctionField W
      ((OpenLineFrameCoordinates318.frame (omega b) (opens b hb (some 0))
        (frame b hb (some 0)) W h).symm
          ((omega b).presheaf.map (homOfLE h).op (referenceSection b hb)))=
      referenceCoefficient b hb:=by
  rw [←OpenLineFrameCoordinates318.inverse_natural (omega b)
    (opens b hb (some 0)) (frame b hb (some 0)) le_rfl h,
    AffineDominantNormRestriction318.germ_restrict]
  rfl
/-- On every dense original common subopen, the local equation is the
GENUINE frame coefficient of the SAME intrinsic dt section. Thus the
rational section is fixed, rather than chosen separately on the charts. -/
theorem actual_dt_coefficient(i:Option (Fin 4))(W:(scheme b).Opens)[Nonempty W]
    (hi:W≤opens b hb i)(href:W≤opens b hb (some 0)):
    (scheme b).germToFunctionField W
      ((OpenLineFrameCoordinates318.frame (omega b) (opens b hb i) (frame b hb i) W hi).symm
        ((omega b).presheaf.map (homOfLE href).op (referenceSection b hb)))=
      localEquation b hb i:=
  ActualLineRationalEquations318.section_coefficient (omega b) (opens b hb) (frame b hb)
    (some 0) (referenceCoefficient b hb) i W hi href
    ((omega b).presheaf.map (homOfLE href).op (referenceSection b hb))
    (reference_on_subopen b hb W href)
/-- The actual line glued from these unit ratios is precisely the SAME
original intrinsic Omega. Identifying its local-equation valuations with
the previous explicit dt coefficient divisor remains a separate comparison. -/
@[expose] def associatedLine:
    omega b≅CocycleModule318.object (opens b hb)
      (FourRootCanonicalTransitionReconstruction318.transitions b hb):=
  ActualLineRationalEquations318.associatedLineIso (omega b) (opens b hb) (frame b hb)
    (cover_top b hb)
end FourRootCanonicalRationalEquations318
