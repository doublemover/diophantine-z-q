module
public import AlgebraicFormalSubgroup318
public import OddSubgroupSign318
public import OddProductHeight318
public section
namespace UnitPlaceOddSigns318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 NumberField
open GlobalNormCoset318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def formalSubgroup (w:FinitePlace K) : AddSubgroup E.Point :=
  AlgebraicFormalSubgroup318.formalSubgroup w.val (FinitePlace.add_le w) D
    (ActualDuplicationPlaces318.finite_coefficients w).1

@[simp] lemma mem_formal (w:FinitePlace K) (Q:E.Point) :
    Q∈formalSubgroup w ↔ Q=0 ∨ 1<w (Q.xRep 0) := Iff.rfl

lemma T_not_formal (w:FinitePlace K) : T 0∉formalSubgroup w := by
  rw [mem_formal]
  simp [T,torsionX,Point.xRep]

lemma multiple_abscissa_ne_zero (n:ℤ) (hn:n≠0) : (n • P).xRep 0≠0 := by
  have hh:=RealMultiples318.multiple_P_abscissa_gt_one ActualQuadraticEmbeddings318.positiveEmbedding n hn
  intro he
  rw [he,map_zero] at hh
  norm_num at hh

lemma translate_formal_of_small (w:FinitePlace K) (hD:w D=1)
    (Q:E.Point) (hQ:Q.xRep 0≠0) (hx:w (Q.xRep 0)<1) : Q+T 0∈formalSubgroup w := by
  cases Q with
  | zero =>
    change w ((0:E.Point).xRep 0)<1 at hx
    simpa only [Point.xRep_zero,Matrix.cons_val_zero,map_one,lt_self_iff_false] using hx
  | some x y h =>
    simp only [Point.xRep_some,Matrix.cons_val_zero] at hQ hx
    obtain ⟨yy,hh,he⟩:=add_zero_torsion_x x y h hQ
    rw [he,mem_formal]
    right
    simp only [Point.xRep_some,Matrix.cons_val_zero,map_div₀,map_neg_eq_map,hD]
    exact (one_lt_div (w.val.pos hQ)).mpr hx

/-- At every actual D-unit finite place, all odd-labelled abscissae have
one common weak sign. The subgroup used is the actual algebraic formal
neighbourhood, not an assumed reduction or logarithm kernel. -/
theorem unit_place_common_sign {ι:Type*} (w:FinitePlace K) (hD:w D=1)
    (n:ι→ℤ) (hn:∀i,Odd (n i)) :
    (∀i,w ((n i • P).xRep 0)≤1) ∨ (∀i,1≤w ((n i • P).xRep 0)) := by
  have hh:=OddSubgroupSign318.common_weak_sign (formalSubgroup w) P (T 0)
    (double_T 0) (T_not_formal w) n hn
  rcases hh with hnone|hnone
  · left
    intro i
    apply le_of_not_gt
    intro hi
    exact hnone i ((mem_formal w _).mpr (Or.inr hi))
  · right
    intro i
    apply le_of_not_gt
    intro hi
    have hni:n i≠0 := by intro hz; have ho:=hn i; rw [hz] at ho; norm_num at ho
    exact hnone i (translate_formal_of_small w hD _ (multiple_abscissa_ne_zero _ hni) hi)

theorem unit_place_common_sign_finset {ι:Type*} (w:FinitePlace K) (hD:w D=1)
    (s:Finset ι) (n:ι→ℤ) (hn:∀i∈s,Odd (n i)) :
    (∀i∈s,w ((n i • P).xRep 0)≤1) ∨ (∀i∈s,1≤w ((n i • P).xRep 0)) := by
  have hh:=unit_place_common_sign w hD (fun i:{i//i∈s}=>n i) (fun i=>hn i i.2)
  rcases hh with h|h
  · exact Or.inl (fun i hi=>h ⟨i,hi⟩)
  · exact Or.inr (fun i hi=>h ⟨i,hi⟩)

#print axioms unit_place_common_sign
#print axioms unit_place_common_sign_finset
end
end UnitPlaceOddSigns318
