module
public import LiteralFrameTorsorMaps318
public import EtaleSectionTrivialization318
public section
noncomputable section
namespace LiteralFrameTorsorGeometric318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralFrameTorsorMaps318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) [NeZero N]
/-- Each geometric fiber is a bijection of actual Scheme maps, by the
unique GL2 change between the actual first and second geometric frames. -/
theorem all_geometric : EtaleSectionTrivialization318.GeometricBijective
    (projection N) (graph N) (graph_projection N):=by
  intro F _ _ b
  obtain ⟨φ,hφ⟩:=Spec.map_surjective (b ≫ base N)
  letI : Algebra (OpenJModel318.Base N) F:=φ.hom.toAlgebra
  let s : LiteralIndependentGeometricBases318.Sections N F:=⟨b,hφ.symm⟩
  constructor
  · intro g h he
    have hp:=congrArg (fun t=>t.val ≫ second N) he
    have hc:LiteralIndependentSectionAction318.action N (Spec.map φ) g s=
        LiteralIndependentSectionAction318.action N (Spec.map φ) h s:=by
      apply Subtype.ext
      rw [LiteralIndependentSectionAction318.action_val,LiteralIndependentSectionAction318.action_val]
      simpa only [EtaleSectionTrivialization318.value,Category.assoc,graph_second] using hp
    obtain ⟨k,hk,hu⟩:=LiteralGeometricFrameTransitivity318.exists_unique N F s
      (LiteralIndependentSectionAction318.action N (Spec.map φ) h s)
    exact (hu g hc).trans (hu h rfl).symm
  · intro t
    let r : LiteralIndependentGeometricBases318.Sections N F:=⟨t.val ≫ second N,by
      change (t.val ≫ pullback.snd (base N) (base N)) ≫ base N=Spec.map φ
      rw [Category.assoc,←pullback.condition,←Category.assoc]
      exact (congrArg (fun q=>q ≫ base N) t.property).trans hφ.symm⟩
    obtain ⟨g,hg,_⟩:=LiteralGeometricFrameTransitivity318.exists_unique N F s r
    refine ⟨g,?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · change (b ≫ graph N g) ≫ projection N=t.val ≫ projection N
      rw [Category.assoc,graph_projection,Category.comp_id,t.property]
    · change (b ≫ graph N g) ≫ second N=t.val ≫ second N
      rw [Category.assoc,graph_second]
      exact congrArg Subtype.val hg
end LiteralFrameTorsorGeometric318
