module
public import ModuleGlobalSections318
public section
noncomputable section
namespace ModuleLocalGluing318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}}
@[expose] def res (M : X.Modules) {U V : X.Opens} (h : V≤U) : Γ(M,U) → Γ(M,V) :=
  M.presheaf.map (homOfLE h).op

theorem res_res (M : X.Modules) {U V W : X.Opens} (h : V≤U) (k : W≤V) (s : Γ(M,U)) :
    res M k (res M h s)=res M (k.trans h) s := by
  exact (CategoryTheory.Functor.map_comp_apply M.presheaf (homOfLE h).op (homOfLE k).op s).symm

theorem res_self (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) : res M le_rfl s=s := by
  change M.presheaf.map (𝟙 (op U)) s=s
  rw [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply]

/-- Compatible linear maps on all subopens of an ambient open cover. -/
structure LocalData (M N : X.Modules) {ι : Type u} (U : ι → X.Opens) where
  map : ∀ i V, V≤U i → (Γ(M,V) →ₗ[Γ(X,V)] Γ(N,V))
  natural : ∀ i V W (hV : V≤U i) (hW : W≤V) (s : Γ(M,V)),
    res N hW (map i V hV s)=map i W (hW.trans hV) (res M hW s)
  compatible : ∀ i j V (hi : V≤U i) (hj : V≤U j) (s : Γ(M,V)),
    map i V hi s=map j V hj s

variable {M N : X.Modules} {ι : Type u} {U : ι → X.Opens}
    (D : LocalData M N U) (hc : ⊤ ≤ iSup  U)

@[expose] def cover (W : X.Opens) (i : ι) : X.Opens := W⊓U i

include hc in
theorem cover_le (W : X.Opens) : W ≤ iSup  (cover (U:=U) W) := by
  intro x hx
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hc (show x∈(⊤:X.Opens) from trivial))
  exact Opens.mem_iSup.mpr ⟨i,hx,hi⟩

@[expose] def pieces (W : X.Opens) (s : Γ(M,W)) (i : ι) : Γ(N,cover (U:=U) W i) :=
  D.map i _ inf_le_right (res M inf_le_left s)

theorem pieces_compatible (W : X.Opens) (s : Γ(M,W)) :
    TopCat.Presheaf.IsCompatible N.presheaf (cover (U:=U) W) (pieces D W s) := by
  intro i j
  change res N inf_le_left (D.map i _ inf_le_right (res M inf_le_left s))=
    res N inf_le_right (D.map j _ inf_le_right (res M inf_le_left s))
  rw [D.natural,D.natural,res_res,res_res]
  exact D.compatible i j _ _ _ _

@[expose] def value (W : X.Opens) (s : Γ(M,W)) : Γ(N,W) :=
  Classical.choose (TopCat.Sheaf.existsUnique_gluing'
    (⟨N.presheaf,N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (cover (U:=U) W) W (fun _ => homOfLE inf_le_left) (cover_le hc W)
    (pieces D W s) (pieces_compatible D W s))

theorem value_restrict (W : X.Opens) (s : Γ(M,W)) (i : ι) :
    res N (show cover (U:=U) W i≤W from inf_le_left) (value D hc W s)=pieces D W s i :=
  (Classical.choose_spec (TopCat.Sheaf.existsUnique_gluing'
    (⟨N.presheaf,N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (cover (U:=U) W) W (fun _ => homOfLE inf_le_left) (cover_le hc W)
    (pieces D W s) (pieces_compatible D W s))).1 i

theorem value_subopen (W V : X.Opens) (h : V≤W) (i : ι) (hi : V≤U i) (s : Γ(M,W)) :
    res N h (value D hc W s)=D.map i V hi (res M h s) := by
  have he : h=(show V≤cover (U:=U) W i from le_inf h hi).trans inf_le_left := Subsingleton.elim _ _
  rw [he,←res_res N (show cover (U:=U) W i≤W from inf_le_left),value_restrict]
  change res N (le_inf h hi) (D.map i _ inf_le_right (res M inf_le_left s))=_
  rw [D.natural,res_res]

include hc in
/-- Equality of sections is detected on the same ambient open cover. -/
theorem ext_value (W : X.Opens) (s t : Γ(N,W))
    (h : ∀ i, res N (show cover (U:=U) W i≤W from inf_le_left) s=
      res N (show cover (U:=U) W i≤W from inf_le_left) t) : s=t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf,N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (cover (U:=U) W) W (fun _ => homOfLE inf_le_left) (cover_le hc W) s t h

theorem value_add (W : X.Opens) (s t : Γ(M,W)) :
    value D hc W (s+t)=value D hc W s+value D hc W t := by
  apply ext_value hc W
  intro i
  rw [value_restrict]
  change D.map i _ inf_le_right (res M inf_le_left (s+t))=
    N.presheaf.map (homOfLE inf_le_left).op (value D hc W s+value D hc W t)
  rw [map_add]
  change _=res N inf_le_left (value D hc W s)+res N inf_le_left (value D hc W t)
  rw [value_restrict,value_restrict]
  change D.map i _ inf_le_right (M.presheaf.map (homOfLE inf_le_left).op (s+t))=_
  rw [map_add,map_add]
  rfl

theorem value_smul (W : X.Opens) (a : Γ(X,W)) (s : Γ(M,W)) :
    value D hc W (a • s)=a • value D hc W s := by
  apply ext_value hc W
  intro i
  rw [value_restrict]
  change D.map i _ inf_le_right (M.presheaf.map (homOfLE inf_le_left).op (a • s))=
    N.presheaf.map (homOfLE inf_le_left).op (a • value D hc W s)
  rw [Scheme.Modules.map_smul,Scheme.Modules.map_smul]
  change _=_ • res N inf_le_left (value D hc W s)
  rw [value_restrict,LinearMap.map_smul]
  rfl

theorem value_natural (W V : X.Opens) (h : V≤W) (s : Γ(M,W)) :
    res N h (value D hc W s)=value D hc V (res M h s) := by
  apply ext_value hc V
  intro i
  rw [res_res,value_restrict]
  rw [value_subopen D hc W (cover (U:=U) V i) (inf_le_left.trans h) i inf_le_right]
  change _=D.map i _ inf_le_right (res M inf_le_left (res M h s))
  rw [res_res]
  rfl

/-- The glued map is genuinely linear over each actual section ring. -/
@[expose] def linear (W : X.Opens) : Γ(M,W) →ₗ[Γ(X,W)] Γ(N,W) where
  toFun := value D hc W
  map_add' := value_add D hc W
  map_smul' := value_smul D hc W

/-- Actual sheaf morphism glued from compatible local linear maps. -/
@[expose] def hom : M ⟶ N where
  val.app W := ModuleCat.ofHom (linear D hc W.unop)
  val.naturality f := by
    ext s
    exact (value_natural D hc _ _ (leOfHom f.unop) s).symm
end ModuleLocalGluing318
