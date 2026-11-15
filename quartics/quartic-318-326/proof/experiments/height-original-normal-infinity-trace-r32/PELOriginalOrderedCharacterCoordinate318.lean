module
public import PELOriginalManuscriptNormalization318
public import ComplexSphereInfinityQuadruple318
public import PELOriginalNormalizedDoubleCover318
public section
noncomputable section
namespace PELOriginalOrderedCharacterCoordinate318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELOriginalMarkedSphere318
open PELOriginalCharacterBranches318 PELOriginalDirectCharacterBranches318
open PELOriginalManuscriptNormalization318
open ComplexSphereFourPointNormalization318
open PELOriginalCharacterQuotient318
local instance : ChartedSpace ℂ MaximalBase:=PELMaximalTopologicalAtlas318.maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=PELMaximalComplexAtlas318.maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=ComplexSphereCharts318.sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=ComplexSphereCharts318.sphere_manifold

/-- Fixed actual visible labels, preserving the original coordinate
characters: omitted105,70,42,30 respectively. No arbitrary Fintype order. -/
@[expose] def ordered : Fin 4→Fin 4→Fin 5:=
  ![![4,2,1,0],![4,3,1,0],![4,3,2,0],![4,3,2,1]]
lemma ordered_injective : ∀i,Function.Injective (ordered i):=by decide
lemma visible : ∀i j,InertiaLabels318.fiveLabels (ordered i j) i≠0:=by decide
lemma exhaustive : ∀i k,InertiaLabels318.fiveLabels k i≠0 → ∃j,ordered i j=k:=by decide
@[expose] def visibleEquiv (i:Fin 4) :
    Fin 4≃{j:Fin 5 // InertiaLabels318.fiveLabels j i≠0}:=
  Equiv.ofBijective (fun j=>⟨ordered i j,visible i j⟩)
    ⟨fun _ _ h=>ordered_injective i (congrArg Subtype.val h),by
      intro k
      obtain ⟨j,hj⟩:=exhaustive i k.val k.property
      exact ⟨j,Subtype.ext hj⟩⟩
@[expose] def branches (i:Fin 4) : Fin 4≃CharacterBranchValues i:=
  (visibleEquiv i).trans (PELOriginalDirectCharacterBranches318.branchEnumeration i)
lemma branches_value (i j:Fin 4) : (branches i j).val=branchPoint (ordered i j):=rfl

/-- Exact permutation connecting the arbitrary OLD enumeration with the
new fixed enumeration. No claim that these orders or parameters are equal. -/
@[expose] def oldOrder (i:Fin 4) : Equiv.Perm (Fin 4):=
  (branches i).trans (PELOriginalFourBranchCoordinate318.actualBranches i).symm
lemma oldOrder_exact (i j:Fin 4) :
    PELOriginalFourBranchCoordinate318.actualBranches i (oldOrder i j)=branches i j:=
  (PELOriginalFourBranchCoordinate318.actualBranches i).apply_symm_apply _

@[expose] def points (i j:Fin 4) : OnePoint ℂ:=
  PELOriginalManuscriptNormalization318.coordinate (branches i j).val
lemma points_injective (i:Fin 4) : Function.Injective (points i):=by
  intro j k h
  apply (branches i).injective
  apply Subtype.ext
  exact PELOriginalManuscriptNormalization318.coordinate.injective h

lemma literal_points (i:Fin 4) : points i=
    (![![∞,(1:ℂ),(lambda:ℂ),(mu:ℂ)],![∞,(0:ℂ),(lambda:ℂ),(mu:ℂ)],
      ![∞,(0:ℂ),(1:ℂ),(mu:ℂ)],![∞,(0:ℂ),(1:ℂ),(lambda:ℂ)]]:
      Fin 4→Fin 4→OnePoint ℂ) i := by
  funext j
  change PELOriginalManuscriptNormalization318.coordinate (branchPoint (ordered i j))=_
  rw [congrFun PELOriginalManuscriptNormalization318.values (ordered i j)]
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def parameter (i:Fin 4) : ℂ:=
  ComplexSphereFourPointNormalization318.parameter (points i) (points_injective i)
@[expose] def coordinate (i:Fin 4) : MaximalBase≃ₜOnePoint ℂ:=
  PELOriginalManuscriptNormalization318.coordinate.trans
    (normalization (points i) (points_injective i))

/-- Actual cross-ratios with the manuscript's fixed labels. These are the
four expressions consumed by the published quartic-invariant solver, in
coordinate-character order105,70,42,30, NOT row order30,42,70,105. -/
theorem parameter_formula (i:Fin 4) : parameter i=
    (![(mu-1)/(lambda-1),mu/lambda,mu,lambda]:Fin 4→ℂ) i := by
  unfold parameter
  have hp:=points_injective i
  rw [literal_points] at hp ⊢
  fin_cases i <;> rw [ComplexSphereInfinityQuadruple318.parameter_eq] <;> simp

lemma parameter_nonexceptional (i:Fin 4) : parameter i≠0 ∧ parameter i≠1:=
  ⟨parameter_ne_zero _ _,parameter_ne_one _ _⟩
lemma coordinate_biholomorphic (i:Fin 4) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coordinate i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coordinate i).symm:=by
  have hn:=normalization_biholomorphic (points i) (points_injective i)
  exact ⟨hn.1.comp PELOriginalManuscriptNormalization318.biholomorphic.1,
    PELOriginalManuscriptNormalization318.biholomorphic.2.comp hn.2⟩
lemma branch_values (i:Fin 4) :
    (fun j:Fin 4=>coordinate i (branches i j).val)=
      ![∞,(0:ℂ),(1:ℂ),(parameter i:ℂ)] := by
  funext j
  fin_cases j
  · exact normalization_zero _ _
  · exact normalization_one _ _
  · exact normalization_two _ _
  · exact normalization_three _ _

/-- Every original branch value, and only those values, is retained after
this explicitly labeled coordinate change. -/
theorem actual_branch_values (i:Fin 4) (q:MaximalBase) :
    q∈CharacterBranchValues i ↔ coordinate i q=∞ ∨ coordinate i q=(0:ℂ) ∨
      coordinate i q=(1:ℂ) ∨ coordinate i q=(parameter i:ℂ) := by
  have hv:=branch_values i
  constructor
  · intro hq
    obtain ⟨j,hj⟩:=(branches i).surjective ⟨q,hq⟩
    have he:=congrArg (fun r:CharacterBranchValues i=>coordinate i r.val) hj
    have hh:=congrFun hv j
    rw [he] at hh
    fin_cases j <;> simp_all
  · intro hq
    have hex:∃j:Fin 4,coordinate i q=coordinate i (branches i j).val:=by
      rcases hq with h|h|h|h
      · exact ⟨0,h.trans (congrFun hv 0).symm⟩
      · exact ⟨1,h.trans (congrFun hv 1).symm⟩
      · exact ⟨2,h.trans (congrFun hv 2).symm⟩
      · exact ⟨3,h.trans (congrFun hv 3).symm⟩
    obtain ⟨j,hj⟩:=hex
    rw [(coordinate i).injective hj]
    exact (branches i j).property

/-- Exact target change relating the old unlabelled normalization to the
new manuscript-labelled normalization on the SAME original cover. -/
@[expose] def oldToNew (i:Fin 4) : OnePoint ℂ≃ₜOnePoint ℂ:=
  (PELOriginalFourBranchCoordinate318.coordinate i).symm.trans (coordinate i)
lemma oldToNew_biholomorphic (i:Fin 4) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (oldToNew i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (oldToNew i).symm:=by
  exact ⟨(coordinate_biholomorphic i).1.comp
      (PELOriginalFourBranchCoordinate318.coordinate_biholomorphic i).2,
    (PELOriginalFourBranchCoordinate318.coordinate_biholomorphic i).1.comp
      (coordinate_biholomorphic i).2⟩
@[expose] def normalizedMap (i:Fin 4) : CharacterBase i→OnePoint ℂ:=coordinate i∘toMaximal i
lemma original_map_comparison (i:Fin 4) (x:CharacterBase i) :
    oldToNew i (PELOriginalNormalizedDoubleCover318.normalizedMap i x)=normalizedMap i x:=by
  change coordinate i ((PELOriginalFourBranchCoordinate318.coordinate i).symm
    (PELOriginalFourBranchCoordinate318.coordinate i (toMaximal i x)))=_
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- Exact full fibers remain one at precisely the four newly specified
coordinates and two at every other point of this same target. -/
theorem all_fibers (i:Fin 4) (z:OnePoint ℂ) :
    Nat.card {x:CharacterBase i // normalizedMap i x=z}=
      if z=∞ ∨ z=(0:ℂ) ∨ z=(1:ℂ) ∨ z=(parameter i:ℂ) then 1 else 2 := by
  classical
  obtain ⟨q,rfl⟩:=(coordinate i).surjective z
  let e : {x:CharacterBase i // normalizedMap i x=coordinate i q}≃
      {x:CharacterBase i // toMaximal i x=q} :=
    {toFun:=fun x=>⟨x.val,(coordinate i).injective x.property⟩
     invFun:=fun x=>⟨x.val,congrArg (coordinate i) x.property⟩
     left_inv:=fun _=>rfl
     right_inv:=fun _=>rfl}
  rw [Nat.card_congr e]
  have he:=actual_branch_values i q
  change Nat.card {x:CharacterBase i // toMaximal i x=q}=1 ↔ _ at he
  split_ifs with h
  · exact he.mpr h
  · rcases PELOriginalNormalizedDoubleCover318.original_fiber_alternatives i q with hh|hh
    · exact False.elim (h (he.mp hh))
    · exact hh
end PELOriginalOrderedCharacterCoordinate318
