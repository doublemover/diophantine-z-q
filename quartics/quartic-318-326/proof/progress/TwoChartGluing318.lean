module
public import Mathlib.Topology.Gluing
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public section
noncomputable section
open Topology TopologicalSpace CategoryTheory
namespace TwoChartGluing318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {X Y:Type} [TopologicalSpace X] [TopologicalSpace Y]

@[expose] def spaces : Bool → TopCat
  | false => TopCat.of X
  | true => TopCat.of Y

@[expose] def overlaps (e:OpenPartialHomeomorph X Y) :
    ∀i:Bool, Bool→Opens (spaces (X:=X) (Y:=Y) i)
  | false,false => ⊤
  | false,true => ⟨e.source,e.open_source⟩
  | true,false => ⟨e.target,e.open_target⟩
  | true,true => ⊤

@[expose] def transitions (e:OpenPartialHomeomorph X Y) :
    ∀i j:Bool, (Opens.toTopCat _).obj (overlaps e i j) ⟶
      (Opens.toTopCat _).obj (overlaps e j i)
  | false,false => 𝟙 _
  | true,true => 𝟙 _
  | false,true => TopCat.ofHom ⟨e.toHomeomorphSourceTarget,e.toHomeomorphSourceTarget.continuous⟩
  | true,false => TopCat.ofHom ⟨e.toHomeomorphSourceTarget.symm,e.toHomeomorphSourceTarget.symm.continuous⟩

@[expose] def core (e:OpenPartialHomeomorph X Y) : TopCat.GlueData.MkCore where
  J := Bool
  U := spaces (X:=X) (Y:=Y)
  V := overlaps e
  t := transitions e
  V_id := by intro i;cases i <;> rfl
  t_id := by intro i;cases i <;> rfl
  t_inter := by
    intro i j k x hx
    cases i <;> cases j <;> cases k <;>
      simp only [overlaps,transitions,TopCat.hom_ofHom,ContinuousMap.toFun_eq_coe,
        CategoryTheory.id_apply,TopologicalSpace.Opens.mem_top] at *
    all_goals first | trivial | exact hx | exact x.property |
      exact (e.toHomeomorphSourceTarget x).property |
      exact (e.toHomeomorphSourceTarget.symm x).property
  cocycle := by
    intro i j k x hx
    cases i <;> cases j <;> cases k <;>
      simp only [transitions,TopCat.hom_ofHom,CategoryTheory.id_apply]
    all_goals first | rfl | exact congrArg Subtype.val (e.toHomeomorphSourceTarget.symm_apply_apply x) |
      exact congrArg Subtype.val (e.toHomeomorphSourceTarget.apply_symm_apply x)

@[expose] def data (e:OpenPartialHomeomorph X Y) : TopCat.GlueData := TopCat.GlueData.mk' (core e)

abbrev Space (e:OpenPartialHomeomorph X Y) := (data e).toGlueData.glued

@[expose] def left (e:OpenPartialHomeomorph X Y) : X→Space e := (data e).toGlueData.ι false
@[expose] def right (e:OpenPartialHomeomorph X Y) : Y→Space e := (data e).toGlueData.ι true

theorem left_isOpenEmbedding (e:OpenPartialHomeomorph X Y) : IsOpenEmbedding (left e) :=
  (data e).ι_isOpenEmbedding false

theorem right_isOpenEmbedding (e:OpenPartialHomeomorph X Y) : IsOpenEmbedding (right e) :=
  (data e).ι_isOpenEmbedding true

theorem left_eq_right_iff (e:OpenPartialHomeomorph X Y) (x:X) (y:Y) :
    left e x=right e y ↔ x∈e.source ∧ e x=y := by
  rw [show left e x=right e y ↔ (data e).Rel ⟨false,x⟩ ⟨true,y⟩ from
    (data e).ι_eq_iff_rel false true x y]
  change (∃a:e.source, a.val=x ∧ e a=y) ↔ _
  constructor
  · rintro ⟨a,rfl,ha⟩
    exact ⟨a.property,ha⟩
  · rintro ⟨hx,hxy⟩
    exact ⟨⟨x,hx⟩,rfl,hxy⟩

theorem jointly_surjective (e:OpenPartialHomeomorph X Y) (z:Space e) :
    (∃x,left e x=z) ∨ (∃y,right e y=z) := by
  obtain ⟨i,w,hw⟩ := (data e).ι_jointly_surjective z
  cases i
  · exact Or.inl ⟨w,hw⟩
  · exact Or.inr ⟨w,hw⟩

end TwoChartGluing318
