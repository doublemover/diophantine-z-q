module
public import OddProductHeight318
public import RawOddAnchorPoints318
public import GlobalIndexHeight318
public section
noncomputable section
namespace RawProductHeight318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawOddAnchorPoints318 GlobalSaturationHeight318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency.types false

/-- The literal source product coordinates, before taking a norm or square. -/
@[expose] def Kprod (w:Assignment) : K := pair (w 143) (w 144)

/-- Exactly the maximum of the four absolute integer labels. No artificial
lower cutoff is inserted. -/
@[expose] def maxIndex (labels:Fin 4→ℤ) : ℕ :=
  Finset.univ.sup (fun i=> (labels i).natAbs)

/-- Rows 100--105 identify the actual field-valued root product. -/
theorem source_product (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    Kprod w=∏i,RawAnchorNorm318.root w i := by
  change pair (w 143) (w 144)=∏i,RawAnchorNorm318.root w i
  have h100 : r100 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=100)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r100] at h100
  have h101 : r101 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=101)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r101] at h101
  have h102 : r102 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=102)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r102] at h102
  have h103 : r103 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=103)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r103] at h103
  have h104 : r104 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=104)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r104] at h104
  have h105 : r105 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=105)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r105] at h105
  have hp : pair (w 139) (w 140)=RawAnchorNorm318.root w 0*RawAnchorNorm318.root w 1 := by
    change pair (w 139) (w 140)=pair (w 79) (w 80)*pair (w 82) (w 83)
    rw [pair_product]
    ext <;> simp only [pair] <;> [linear_combination h100; linear_combination h101]
  have hp2 : pair (w 141) (w 142)=RawAnchorNorm318.root w 2*pair (w 139) (w 140) := by
    change pair (w 141) (w 142)=pair (w 85) (w 86)*pair (w 139) (w 140)
    rw [pair_product]
    ext <;> simp only [pair] <;> [linear_combination h102; linear_combination h103]
  have hp3 : pair (w 143) (w 144)=RawAnchorNorm318.root w 3*pair (w 141) (w 142) := by
    change pair (w 143) (w 144)=pair (w 88) (w 89)*pair (w 141) (w 142)
    rw [pair_product]
    ext <;> simp only [pair] <;> [linear_combination h104; linear_combination h105]
  rw [hp3,hp2,hp,Fin.prod_univ_four]
  ring

lemma root_square_eq_abscissa (w:Assignment) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) (i:Fin 4) :
    (RawAnchorNorm318.root w i)^2=((labels i) • P).xRep 0 := by
  obtain ⟨y,h,hpt⟩ := hlabels i
  rw [hpt]
  simp only [Point.xRep_some,Matrix.cons_val_zero]

/-- The product whose height is used in the source is Kprod squared,
not the norm and not the product of the unsquared heights. -/
theorem source_squared_product (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) :
    (Kprod w)^2=∏i,((labels i) • P).xRep 0 := by
  rw [source_product S w source,←Finset.prod_pow]
  exact Finset.prod_congr rfl (fun i _=>root_square_eq_abscissa w labels hlabels i)

lemma maxIndex_attained (labels:Fin 4→ℤ) :
    ∃i,maxIndex labels=(labels i).natAbs := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ
    (by simp : (Finset.univ:Finset (Fin 4)).Nonempty) (fun i=>(labels i).natAbs)
  exact ⟨i,hi⟩

lemma label_le_maxIndex (labels:Fin 4→ℤ) (i:Fin 4) :
    (labels i).natAbs≤maxIndex labels := by
  exact Finset.le_sup (f:=fun j=>(labels j).natAbs) (Finset.mem_univ i)

lemma label_abs_le_maxIndex (labels:Fin 4→ℤ) (i:Fin 4) :
    |(labels i:ℝ)|≤(maxIndex labels:ℝ) := by
  have hh : ((labels i).natAbs:ℝ)≤(maxIndex labels:ℝ) := by
    exact_mod_cast label_le_maxIndex labels i
  simpa using hh

/-- Either sign choice in the literal translated scalar label gives the same
bound |c|≤B+1, with the exact maximum B. -/
lemma scalar_abs_le_maxIndex_add_one (labels:Fin 4→ℤ) (c:ℤ)
    (hc:c=labels 1-1 ∨ c= -labels 1-1) :
    (c.natAbs:ℝ)≤(maxIndex labels:ℝ)+1 := by
  have hn := label_abs_le_maxIndex labels 1
  have he : (c.natAbs:ℝ)=|(c:ℝ)| := by simp
  rw [he]
  rcases hc with hc|hc
  · have hc' : (c:ℝ)=(labels 1:ℝ)-1 := by exact_mod_cast hc
    rw [hc']
    have hh := abs_sub (labels 1:ℝ) 1
    norm_num at hh
    linarith
  · have hc' : (c:ℝ)= -(labels 1:ℝ)-1 := by exact_mod_cast hc
    rw [hc']
    have hh := abs_sub (-(labels 1:ℝ)) 1
    simp only [abs_neg,abs_one] at hh
    linarith

/-- A genuine scalar lower bound supplies B≥3 when downstream separation
needs it. The maximum itself is not modified to enforce this inequality. -/
lemma three_le_maxIndex_of_scalar_bound (labels:Fin 4→ℤ) (c:ℤ)
    (hc:c=labels 1-1 ∨ c= -labels 1-1) (hlarge:4<(c.natAbs:ℝ)) :
    3≤(maxIndex labels:ℝ) := by
  have hh := scalar_abs_le_maxIndex_add_one labels c hc
  linarith

/-- The already-constructed genuine canonical height gives the exact
maximum-index lower bound for the sum of four actual abscissa heights. -/
theorem max_index_sum_lower (labels:Fin 4→ℤ) :
    (maxIndex labels:ℝ)^2-6<∑i,xHeight ((labels i) • P) := by
  obtain ⟨i,hi⟩ := maxIndex_attained labels
  have hh := GlobalIndexHeight318.multiple_height_lower
    ActualCanonicalHeight318.canonical_data (labels i)
  have hs : xHeight ((labels i) • P)≤∑j,xHeight ((labels j) • P) :=
    Finset.single_le_sum (fun j _=>ActualCanonicalHeight318.actual_nonneg ((labels j) • P))
      (Finset.mem_univ i)
  rw [hi]
  have he : ((labels i).natAbs:ℝ)^2=(labels i:ℝ)^2 := by
    simp
  rw [he]
  exact hh.trans_le hs

/-- Named product-height interface: no local property is concealed in this
algebraic and global-height implication. -/
theorem max_index_lower_of_height_identity (w:Assignment) (labels:Fin 4→ℤ)
    (hprod:NumberField.absLogHeight₁ ((Kprod w)^2)=∑i,xHeight ((labels i) • P)) :
    (maxIndex labels:ℝ)^2-6<NumberField.absLogHeight₁ ((Kprod w)^2) := by
  rw [hprod]
  exact max_index_sum_lower labels

/-- Actual source height identity with precisely the common finite-place
weak-sign input exposed. RootLabels already force all labels nonzero. -/
theorem source_height_identity (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels)
    (hf:∀v:NumberField.FinitePlace K,
      (∀i,v (((labels i) • P).xRep 0)≤1) ∨ (∀i,1≤v (((labels i) • P).xRep 0))) :
    NumberField.absLogHeight₁ ((Kprod w)^2)=∑i,xHeight ((labels i) • P) := by
  rw [source_squared_product S w source labels hlabels]
  apply OddProductHeight318.multiple_height_product Finset.univ labels
    (fun i _=>root_labels_nonzero w labels hlabels i)
  intro v
  rcases hf v with h|h
  · exact Or.inl (fun i _=>h i)
  · exact Or.inr (fun i _=>h i)

/-- Exact source maximum B=max_i|n_i| lower bound, with no max3 convention. -/
theorem source_max_index_lower (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels)
    (hf:∀v:NumberField.FinitePlace K,
      (∀i,v (((labels i) • P).xRep 0)≤1) ∨ (∀i,1≤v (((labels i) • P).xRep 0))) :
    (maxIndex labels:ℝ)^2-6<NumberField.absLogHeight₁ ((Kprod w)^2) :=
  max_index_lower_of_height_identity w labels (source_height_identity S w source labels hlabels hf)

#print axioms source_product
#print axioms root_square_eq_abscissa
#print axioms source_squared_product
#print axioms maxIndex_attained
#print axioms label_le_maxIndex
#print axioms label_abs_le_maxIndex
#print axioms scalar_abs_le_maxIndex_add_one
#print axioms three_le_maxIndex_of_scalar_bound
#print axioms max_index_sum_lower
#print axioms max_index_lower_of_height_identity
#print axioms source_height_identity
#print axioms source_max_index_lower
end RawProductHeight318
