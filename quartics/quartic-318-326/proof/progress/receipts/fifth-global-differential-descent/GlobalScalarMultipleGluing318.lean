module
public import ModuleLocalGluing318
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace GlobalScalarMultipleGluing318
open AlgebraicGeometry CategoryTheory Opposite
open ModuleLocalGluing318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} [IsIntegral X] (M:X.Modules)
    {ι:Type u} (U:ι→X.Opens) (hc : ⊤ ≤ iSup U)
    (W:X.Opens) [Nonempty W] (hW:∀i,W≤U i)
    (s t:Γ(M,⊤))
    (hinj:Function.Injective (fun a:Γ(X,W)=>a • res M (show W≤⊤ from le_top) t))
    (a:∀i,Γ(X,U i))
    (ha:∀i,res M (show U i≤⊤ from le_top) s=
      a i • res M (show U i≤⊤ from le_top) t)

@[expose] def ringRes {V Z:X.Opens} (h:Z≤V) (a:Γ(X,V)):Γ(X,Z):=
  X.presheaf.map (homOfLE h).op a

lemma ringRes_ringRes {V Z Y:X.Opens} (h:Z≤V) (k:Y≤Z) (a:Γ(X,V)):
    ringRes k (ringRes h a)=ringRes (k.trans h) a:=
  (Functor.map_comp_apply X.presheaf (homOfLE h).op (homOfLE k).op a).symm

lemma res_smul {V Z:X.Opens} (h:Z≤V) (a:Γ(X,V)) (s:Γ(M,V)):
    res M h (a • s)=ringRes h a • res M h s:=
  Scheme.Modules.map_smul M (homOfLE h) a s

include hW hinj ha in
lemma common_equal (i j:ι):ringRes (hW i) (a i)=ringRes (hW j) (a j):=by
  apply hinj
  have hi:=congrArg (res M (hW i)) (ha i)
  have hj:=congrArg (res M (hW j)) (ha j)
  rw [res_smul,res_res,res_res] at hi hj
  exact hi.symm.trans hj

include hW hinj ha in
lemma compatible:TopCat.Presheaf.IsCompatible X.presheaf U a:=by
  intro i j
  apply map_injective_of_isIntegral X (homOfLE (le_inf (hW i) (hW j)))
  change ringRes (le_inf (hW i) (hW j)) (ringRes inf_le_left (a i))=
    ringRes (le_inf (hW i) (hW j)) (ringRes inf_le_right (a j))
  rw [ringRes_ringRes,ringRes_ringRes]
  exact common_equal M U W hW s t hinj a ha i j

include hc hW hinj ha in
/-- Local regular multiples glue as a genuine global regular function.
Compatibility is checked on whole intersections using integrality and a
common nonempty open where multiplication by the given section is injective. -/
theorem exists_global:∃r:Γ(X,⊤),s=r • t:=by
  obtain ⟨r,hr,_⟩:=TopCat.Sheaf.existsUnique_gluing' X.sheaf U ⊤
    (fun _=>homOfLE le_top) hc a (compatible M U W hW s t hinj a ha)
  change Γ(X,⊤) at r
  refine ⟨r,?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf,M.isSheaf⟩:TopCat.Sheaf AddCommGrpCat X)
    U ⊤ (fun _=>homOfLE le_top) hc s (r • t)
  intro i
  change res M (show U i≤⊤ from le_top) s=res M (show U i≤⊤ from le_top) (r • t)
  rw [res_smul]
  change res M le_top s=ringRes le_top r • res M le_top t
  rw [show ringRes (show U i≤⊤ from le_top) r=a i from hr i]
  exact ha i
end GlobalScalarMultipleGluing318
