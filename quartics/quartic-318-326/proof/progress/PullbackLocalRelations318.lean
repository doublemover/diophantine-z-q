module
public import PullbackScalar318
public import ModuleScalar318
public import LocalCoordinateRelation318
public import PulledCoordinateMaps318
public section
noncomputable section
namespace PullbackLocalRelations318
open AlgebraicGeometry CategoryTheory
open ClutchedModule318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y U V : Scheme.{u}}

theorem pullback_multiply (g : V ⟶ U) (a : Γ(U,⊤)) :
    (Scheme.Modules.pullback g).map (multiply a)=
      ModuleScalar318.map ((Scheme.Modules.pullback g).obj (unit U)) (g.appTop a) := by
  apply (cancel_mono (IdentityCotangent318.pullbackUnitIso g).hom).mp
  rw [PullbackScalar318.pullback_multiply,ModuleScalar318.natural,ModuleScalar318.unit_eq]

variable (p : X ⟶ Y) (j : U ⟶ Y) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (g : V ⟶ U) (h : k≫p=g≫j)

/-- The common domain factor in both coordinate comparisons. Its exact
normalization need not be guessed: the same canonical map occurs for both. -/
@[expose] def domainFactor : (unit X).restrict k ⟶ (Scheme.Modules.pullback g).obj (unit U) :=
  (Scheme.Modules.restrictFunctor k).map (IdentityCotangent318.pullbackUnitIso p).inv ≫
    (PullbackChartNaturality318.chartNatIso p j k g h).hom.app (unit Y) ≫
    (Scheme.Modules.pullback g).map (Scheme.Modules.restrictUnitIso j).hom

theorem factorization {L : Y.Modules} (f : unit Y ⟶ L) :
    (Scheme.Modules.restrictFunctor k).map (PulledCoordinateMaps318.map p f)=
      domainFactor p j k g h ≫
      (Scheme.Modules.pullback g).map (LocalCoordinateRelation318.localMap j f) ≫
      (PullbackChartNaturality318.chartNatIso p j k g h).inv.app L := by
  apply (cancel_mono ((PullbackChartNaturality318.chartNatIso p j k g h).hom.app L)).mp
  have hn := (PullbackChartNaturality318.chartNatIso p j k g h).hom.naturality f
  simp only [Functor.comp_map] at hn
  unfold PulledCoordinateMaps318.map domainFactor
  rw [Functor.map_comp]
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id]
  rw [hn]
  rw [LocalCoordinateRelation318.localMap_recover j f,Functor.map_comp]
  rfl

include h in
/-- The exact target coordinate ratio pulls back to the exact source regular
function, for the literal pulled coordinate morphisms. -/
theorem relation {L : Y.Modules} (f₀ f₁ : unit Y ⟶ L) (a : Γ(U,⊤))
    (hr : LocalCoordinateRelation318.localMap j f₁=
      multiply a ≫ LocalCoordinateRelation318.localMap j f₀) :
    (Scheme.Modules.restrictFunctor k).map (PulledCoordinateMaps318.map p f₁)=
      (Scheme.Modules.restrictFunctor k).map (PulledCoordinateMaps318.map p f₀) ≫
      ModuleScalar318.map (((Scheme.Modules.pullback p).obj L).restrict k) (g.appTop a) := by
  rw [factorization p j k g h f₁,factorization p j k g h f₀,hr,Functor.map_comp,
    pullback_multiply]
  have hn := ModuleScalar318.natural
    (N:=(((Scheme.Modules.pullback p).obj L).restrict k)) (g.appTop a)
    ((Scheme.Modules.pullback g).map (LocalCoordinateRelation318.localMap j f₀) ≫
      (PullbackChartNaturality318.chartNatIso p j k g h).inv.app L)
  simpa only [Category.assoc] using congrArg (fun q => domainFactor p j k g h ≫ q) hn
end PullbackLocalRelations318
