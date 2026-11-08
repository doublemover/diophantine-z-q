module
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public section
noncomputable section
namespace GeometricIntegralDenseOpen318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
local instance integralIsoClosed :
    ObjectProperty.IsClosedUnderIsomorphisms (C:=Scheme.{u}) IsIntegral where
  of_iso e h:=by
    letI:=h
    exact IsIntegral.of_isIso e.hom
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A quasi-compact schematically dense integral source forces its target
to be integral. Both reducedness and topological irreducibility descend. -/
theorem integral_of_schematicallyDominant {U X:Scheme} (i:U⟶X)
    [QuasiCompact i] [IsSchemeTheoreticallyDominant i] [IsIntegral U] : IsIntegral X:=by
  letI:IsReduced X:=IsSchemeTheoreticallyDominant.isReduced i
  have hr:IsIrreducible (Set.range i):=by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ U).image i i.continuous.continuousOn
  haveI:IrreducibleSpace X:=irreducibleSpace_def X |>.mpr (by
    change IsIrreducible (Set.univ:Set X)
    rw [←i.denseRange.closure_range]
    exact hr.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- A nonempty quasi-compact open of an integral scheme over a field detects
geometric integrality. The proof uses flat base change of schematic density,
so it controls nilpotents rather than only field-valued points. -/
theorem of_dense_open {k:Type u} [Field k] {U X:Scheme.{u}} (i:U⟶X)
    (f:X⟶Spec (CommRingCat.of k)) [IsIntegral X] [Nonempty U]
    [IsOpenImmersion i] [QuasiCompact i] [GeometricallyIntegral (i≫f)] :
    GeometricallyIntegral f:=by
  letI:IsDominant i:=⟨IsOpenMap.denseRange_of_isPreirreducibleSpace i i.isOpenEmbedding.isOpenMap⟩
  letI:IsSchemeTheoreticallyDominant i:=IsSchemeTheoreticallyDominant.of_isDominant i
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro F _ _
  let g:=Spec.map (CommRingCat.ofHom (algebraMap k F))
  haveI:IsIntegral (pullback (i≫f) g):=inferInstance
  haveI:IsIntegral (pullback i (pullback.fst f g)):=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso f g i).inv
  exact integral_of_schematicallyDominant (pullback.snd i (pullback.fst f g))
end GeometricIntegralDenseOpen318
