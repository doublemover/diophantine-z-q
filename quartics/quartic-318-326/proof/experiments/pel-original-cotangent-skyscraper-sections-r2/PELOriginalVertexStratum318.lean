module
public import PELOriginalComparisonHomeomorph318
public section
noncomputable section
namespace PELOriginalVertexStratum318
open QuaternionicJointPeriodTopology318 PELJointNormOneAction318
open PELEffectiveNormOneAction318 PELUnlevelledComplexBase318
open PELDirichletHeight318 PELDirichletSidePairingData318 PELDirichletVertexCycles318
open PELOriginalActualVertexGluing318 PELOriginalSideQuotient318
open PELOriginalBoundaryAction318 PELOriginalOrbitRelation318 PELOriginalProjectiveTangents318
set_option maxHeartbeats 1800000

/-- Recover an actual original unit from equality in the effective quotient. -/
theorem projection_eq_iff_unit (τ σ : HalfPlane) :
    projection τ=projection σ ↔ ∃ u : normOneUnits,u • σ=τ := by
  constructor
  · intro h
    obtain ⟨g,hg⟩ := (show ∃ g : effectiveGroup,g • σ=τ from Quotient.exact h)
    obtain ⟨u,rfl⟩ := effectiveMap_surjective g
    exact ⟨u,hg⟩
  · rintro ⟨u,rfl⟩
    exact PELOriginalBaseCompact318.projection_unit u σ

theorem vertex_injective : Function.Injective vertex := by decide

theorem realVertex_injective : Function.Injective (fun v : Fin 28 => realPoint (vertex v)) := by
  intro a b h
  apply vertex_injective
  apply Prod.ext
  · have hA := congrArg Prod.fst h
    exact_mod_cast hA
  · have hB := congrArg Prod.snd h
    exact_mod_cast hB

/-- The five finite graph classes are EXACTLY the five actual arithmetic
vertex orbits, not just a quotient of the list of displayed vertices. -/
theorem vertex_projection_iff (a b : Fin 28) :
    projection (vertexPoint a).val=projection (vertexPoint b).val ↔ vertexClass a=vertexClass b := by
  constructor
  · intro h
    obtain ⟨u,hu⟩ := (projection_eq_iff_unit _ _).mp h
    have hd := orbit_multiplier_one (vertexPoint b) (vertexPoint a) u hu
    rw [vertexPoint_coordinates] at hd
    obtain ⟨w,hw,hact⟩ := original_vertex_action u b (vertexPoint b).val
      (vertexPoint_coordinates b) hd
    rw [hu,vertexPoint_coordinates] at hact
    have he := realVertex_injective hact
    exact (congrArg vertexClass he).trans hw
  · intro h
    exact congrArg arithmeticComparison (same_class_quotient a b h)

@[expose] def representative : Fin 5 → Fin 28 := ![0,2,4,6,8]
theorem representative_class (i : Fin 5) : vertexClass (representative i)=i := by
  fin_cases i <;> rfl

/-- Actual zero-stratum in the unchanged arithmetic curve. -/
@[expose] def VertexImage : Set UnlevelledBase :=
  Set.range (fun v : Fin 28 => projection (vertexPoint v).val)

@[expose] def vertexEnumeration : Fin 5 ≃ VertexImage :=
  Equiv.ofBijective
    (fun i => ⟨projection (vertexPoint (representative i)).val,⟨representative i,rfl⟩⟩)
    ⟨by
      intro i j h
      have he := (vertex_projection_iff (representative i) (representative j)).mp
        (congrArg Subtype.val h)
      simpa only [representative_class] using he,
    by
      intro q
      obtain ⟨v,hv⟩ := q.property
      refine ⟨vertexClass v,?_⟩
      apply Subtype.ext
      exact ((vertex_projection_iff (representative (vertexClass v)) v).mpr
        (representative_class _)).trans hv⟩

theorem actual_vertex_count : Nat.card VertexImage=5 := by
  rw [← Nat.card_congr vertexEnumeration]
  simp
end PELOriginalVertexStratum318
