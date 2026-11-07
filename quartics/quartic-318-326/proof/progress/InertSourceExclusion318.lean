module
public import InertPlace318
public import CompressedOrientation318
public section
namespace InertSourceExclusion318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay
open ConcretePadic318 (rationalPlace)
open RawDetector318 RawWeights318 SourceContact318 FiniteContact318
open CompressedOrientation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable (p:ℕ) [Fact p.Prime] (nonsquare:¬ ∃ x:ZMod p, x^2=2)

@[simp] theorem rational_place (q:ℚ) :
    SourceContact318.rational (InertPlace318.place p nonsquare) q=rationalPlace p q :=
  InertPlace318.place_rational p nonsquare q

theorem place_nat_unit (n:ℕ) (hn:¬p∣n) : InertPlace318.place p nonsquare (n:K)=0 := by
  have heq:(n:K)=pair (n:ℚ) 0 := by ext <;> simp [pair]
  rw [heq,InertPlace318.place_rational,ConcretePadic318.rational_nat_unit p n hn]

/-- The sole inert place is fixed by quadratic conjugation. -/
theorem conjugation_invariant (x:K) :
    InertPlace318.place p nonsquare (conj x)=InertPlace318.place p nonsquare x := by
  obtain ⟨a,b⟩ := x
  change InertPlace318.place p nonsquare (pair a (-b))=InertPlace318.place p nonsquare (pair a b)
  rw [InertPlace318.place_pair,InertPlace318.place_pair,AddValuation.map_neg]

theorem positive_of_norm (x:K) (h:0<rationalPlace p (AnchorNorm318.norm x)) :
    0<InertPlace318.place p nonsquare x := by
  by_contra! hx
  rw [InertPlace318.place_norm p nonsquare,two_nsmul] at h
  exact not_lt_of_ge (add_nonpos hx hx) h

/-- Literal compression forbids both positive norm tests at one inert place.
The only additional constant excluded here is 41; inertness already excludes 2.
No formal logarithm, reduction map, or elliptic group-label input occurs. -/
theorem positive_norms_impossible (nonsquare:¬ ∃ x:ZMod p, x^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hp41:¬p∣41)
    (hH:0<rationalPlace p ((w 33)^2-2*(w 34)^2))
    (hV:0<rationalPlace p ((w 76)^2-2*(w 77)^2)) : False := by
  let v := InertPlace318.place p nonsquare
  have h2:v (2:K)=0 := InertPlace318.place_two p nonsquare
  have h41:v (41:K)=0 := place_nat_unit p nonsquare 41 hp41
  obtain ⟨hk,hm⟩ := good_constants v h2 h41
  have hi:v i=0 := InertPlace318.place_i p nonsquare
  have hD : 0≤v CompressedOrientation318.D := by
    have heq:CompressedOrientation318.D=11-6*i := by
      ext <;> norm_num [CompressedOrientation318.D,i,pair]
    rw [heq]
    apply v.map_le_sub (nat_nonnegative v 11)
    rw [v.map_mul,hi,add_zero]
    exact nat_nonnegative v 6
  have hh : 0<v (fH w) := positive_of_norm p nonsquare _
    (by simpa [fH,AnchorNorm318.norm_pair] using hH)
  have hv : 0<v (fV w) := positive_of_norm p nonsquare _
    (by simpa [fV,AnchorNorm318.norm_pair] using hV)
  have hz := (source_separates S w source v hk hm hD h2).1 hh
  rw [hz] at hv
  exact lt_irrefl _ hv

/-- A positive odd consumed finite contact in literal chain 0 cannot occur
at an inert prime. All leaf, weight, terminal and pole inputs are extracted
from the raw source, not assumed as a new arithmetic certificate. -/
theorem source_contact0_inert_false (nonsquare:¬ ∃ x:ZMod p, x^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A0 S w)=a)
    (hf:rationalPlace p (t0 S w-root j)=f) (hpos:0<f) (hodd:Odd f) : False := by
  let v := InertPlace318.place p nonsquare
  have h2:v (2:K)=0 := InertPlace318.place_two p nonsquare
  have h3:v (3:K)=0 := place_nat_unit p nonsquare 3
    (not_dvd_supported p hgood 3 (by norm_num [contactModulus]))
  have h7:v (7:K)=0 := place_nat_unit p nonsquare 7
    (not_dvd_supported p hgood 7 (by norm_num [contactModulus]))
  have h17:v (17:K)=0 := place_nat_unit p nonsquare 17 hp17
  obtain ⟨hD,hDc⟩ := SourcePadic318.discriminant_units v h2 h3 h7
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t0 S w) j f hf hpos
  have hF' : rationalPlace p (F0 S w)=f := by rw [F0_actual S w source]; exact hF
  have hb := (contact0_extract S w source v a f
    (by simpa only [v,rational_place] using hA)
    (by simpa only [v,rational_place] using hF')
    (by simpa only [v,rational_place,delta0] using hd) hodd hD hDc h2 h3 h17).2
  have hn := common_place_norm_tests S w source v (inputs0 S w)
    (q0_4 S w) (q0_1 S w) (by simp [inputs0]) (by simp [inputs0]) hb
  exact positive_norms_impossible p nonsquare S w source hp41
    (by simpa only [v,rational_place] using hn.1)
    (by simpa only [v,rational_place] using hn.2)

/-- A positive odd consumed finite contact in literal chain 1 cannot occur
at an inert prime. All leaf, weight, terminal and pole inputs are extracted
from the raw source, not assumed as a new arithmetic certificate. -/
theorem source_contact1_inert_false (nonsquare:¬ ∃ x:ZMod p, x^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A1 S w)=a)
    (hf:rationalPlace p (t1 S w-root j)=f) (hpos:0<f) (hodd:Odd f) : False := by
  let v := InertPlace318.place p nonsquare
  have h2:v (2:K)=0 := InertPlace318.place_two p nonsquare
  have h3:v (3:K)=0 := place_nat_unit p nonsquare 3
    (not_dvd_supported p hgood 3 (by norm_num [contactModulus]))
  have h7:v (7:K)=0 := place_nat_unit p nonsquare 7
    (not_dvd_supported p hgood 7 (by norm_num [contactModulus]))
  have h17:v (17:K)=0 := place_nat_unit p nonsquare 17 hp17
  obtain ⟨hD,hDc⟩ := SourcePadic318.discriminant_units v h2 h3 h7
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t1 S w) j f hf hpos
  have hF' : rationalPlace p (F1 S w)=f := by rw [F1_actual S w source]; exact hF
  have hb := (contact1_extract S w source v a f
    (by simpa only [v,rational_place] using hA)
    (by simpa only [v,rational_place] using hF')
    (by simpa only [v,rational_place,delta1] using hd) hodd hD hDc h2 h3 h17).2
  have hn := common_place_norm_tests S w source v (inputs1 S w)
    (q1_4 S w) (q1_1 S w) (by simp [inputs1]) (by simp [inputs1]) hb
  exact positive_norms_impossible p nonsquare S w source hp41
    (by simpa only [v,rational_place] using hn.1)
    (by simpa only [v,rational_place] using hn.2)

/-- A positive odd consumed finite contact in literal chain 2 cannot occur
at an inert prime. All leaf, weight, terminal and pole inputs are extracted
from the raw source, not assumed as a new arithmetic certificate. -/
theorem source_contact2_inert_false (nonsquare:¬ ∃ x:ZMod p, x^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A2 S w)=a)
    (hf:rationalPlace p (t2 S w-root j)=f) (hpos:0<f) (hodd:Odd f) : False := by
  let v := InertPlace318.place p nonsquare
  have h2:v (2:K)=0 := InertPlace318.place_two p nonsquare
  have h3:v (3:K)=0 := place_nat_unit p nonsquare 3
    (not_dvd_supported p hgood 3 (by norm_num [contactModulus]))
  have h7:v (7:K)=0 := place_nat_unit p nonsquare 7
    (not_dvd_supported p hgood 7 (by norm_num [contactModulus]))
  have h17:v (17:K)=0 := place_nat_unit p nonsquare 17 hp17
  obtain ⟨hD,hDc⟩ := SourcePadic318.discriminant_units v h2 h3 h7
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t2 S w) j f hf hpos
  have hF' : rationalPlace p (F2 S w)=f := by rw [F2_actual S w source]; exact hF
  have hb := (contact2_extract S w source v a f
    (by simpa only [v,rational_place] using hA)
    (by simpa only [v,rational_place] using hF')
    (by simpa only [v,rational_place,delta2] using hd) hodd hD hDc h2 h3 h17).2
  have hn := common_place_norm_tests S w source v (inputs2 S w)
    (q2_4 S w) (q2_1 S w) (by simp [inputs2]) (by simp [inputs2]) hb
  exact positive_norms_impossible p nonsquare S w source hp41
    (by simpa only [v,rational_place] using hn.1)
    (by simpa only [v,rational_place] using hn.2)

/-- Every positive odd finite contact in chain 0 forces 2 to be a square
in the residue field. The next p-adic lifting step is intentionally separate. -/
theorem source_contact0_residue_split (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A0 S w)=a)
    (hf:rationalPlace p (t0 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃ x:ZMod p, x^2=2 := by
  by_contra hn
  exact source_contact0_inert_false p hn S w source a f j hgood hp17 hp41 hA hf hpos hodd

/-- Every positive odd finite contact in chain 1 forces 2 to be a square
in the residue field. The next p-adic lifting step is intentionally separate. -/
theorem source_contact1_residue_split (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A1 S w)=a)
    (hf:rationalPlace p (t1 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃ x:ZMod p, x^2=2 := by
  by_contra hn
  exact source_contact1_inert_false p hn S w source a f j hgood hp17 hp41 hA hf hpos hodd

/-- Every positive odd finite contact in chain 2 forces 2 to be a square
in the residue field. The next p-adic lifting step is intentionally separate. -/
theorem source_contact2_residue_split (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A2 S w)=a)
    (hf:rationalPlace p (t2 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃ x:ZMod p, x^2=2 := by
  by_contra hn
  exact source_contact2_inert_false p hn S w source a f j hgood hp17 hp41 hA hf hpos hodd

end InertSourceExclusion318

#print axioms InertSourceExclusion318.rational_place
#print axioms InertSourceExclusion318.place_nat_unit
#print axioms InertSourceExclusion318.conjugation_invariant
#print axioms InertSourceExclusion318.positive_of_norm
#print axioms InertSourceExclusion318.positive_norms_impossible
#print axioms InertSourceExclusion318.source_contact0_inert_false
#print axioms InertSourceExclusion318.source_contact1_inert_false
#print axioms InertSourceExclusion318.source_contact2_inert_false

#print axioms InertSourceExclusion318.source_contact0_residue_split

#print axioms InertSourceExclusion318.source_contact1_residue_split

#print axioms InertSourceExclusion318.source_contact2_residue_split
