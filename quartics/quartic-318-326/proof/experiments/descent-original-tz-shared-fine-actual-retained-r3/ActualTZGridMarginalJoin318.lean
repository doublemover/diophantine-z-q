module
public import ActualTZExactZeroIntegerGrid318
public import ActualTZIntegerGridMarker318
public import ActualTZSparseWrapUnion318
import all ActualTZExactZeroIntegerGrid318
import all ActualTZSignedGridPushforward318
public section
noncomputable section
namespace ActualTZGridMarginalJoin318
open scoped BigOperators
open ActualTZSparseWrapUnion318 ActualTZIntegerGridMarker318
attribute [local instance] Classical.propDecidable

variable {n p : ℕ} {R K : Type*} [Fintype R] [Fintype K]
abbrev Grid (L : Fin n→ℕ) := ActualTZExactZeroIntegerGrid318.Grid L

theorem weighted_marginal [NeZero p] [Fact p.Prime]
    (L : Fin n→ℕ) (s : Fin n→ℤ) (M d : ℕ)
    (hM : 0<M) (hL : ∀ i,M≤L i)
    (D : R→K→MvPolynomial (Fin n) ℤ)
    (hD : ∀ r i,reduced (p:=p) (D r i)≠0) (hDeg : ∀ r i,(D r i).totalDegree≤d)
    (θ : Grid L→R→ℝ) (hθ : ∀ z r,0≤θ z r) (hθ1 : ∀ z r,θ z r≤1)
    (hit : Grid L→R→Prop) (hHit : ∀ z r,hit z r→∃ i,(p:ℤ)∣
      MvPolynomial.eval (fun k=>s k+(z k).val) (D r i)) :
    (∑ z : Grid L,(ActualTZExactZeroIntegerGrid318.uniform L:ℝ)*
      (∑ r : R,θ z r*(if hit z r then 1 else 0)))≤
      (Fintype.card R:ℝ)*(Fintype.card K:ℝ)*
        ((2:ℝ)^n*(n:ℝ)*(d:ℝ))*(1/(p:ℝ)+1/M) := by
  let m (_ : Grid L) := (ActualTZExactZeroIntegerGrid318.uniform L:ℝ)
  let event (z : Grid L) (r : R) (i : K) : Prop :=
    (p:ℤ)∣MvPolynomial.eval (fun k=>s k+(z k).val) (D r i)
  let E := ((2:ℝ)^n*(n:ℝ)*(d:ℝ))*(1/(p:ℝ)+1/M)
  have hE (r : R) (i : K) : (∑ z : Grid L,m z*
      (@ite ℝ (event z r i) (Classical.propDecidable (event z r i)) 1 0))≤E := by
    have H := ActualTZSignedGridPushforward318.probability_le (p:=p) L s M d hM hL
      (reduced (D r i)) (hD r i) ((reduced_degree (p:=p) (D r i)).trans (hDeg r i))
    have HP : (∑ z : Grid L,m z*
        (@ite ℝ (event z r i) (Classical.propDecidable (event z r i)) 1 0))≤
        (2:ℝ)^n*((n:ℝ)*((d:ℝ)/((min M p:ℕ):ℝ))) := by
      calc
        _ = (ActualTZSignedGridPushforward318.probability L s (reduced (p:=p) (D r i)):ℝ) := by
          unfold ActualTZSignedGridPushforward318.probability
          rw [NNRat.cast_sum]
          apply Finset.sum_congr rfl
          intro z _
          have he := residue_root (p:=p) L s z (D r i)
          by_cases h : event z r i
          · have h' := he.mpr h
            simp only [if_pos h,if_pos h',mul_one,m,ActualTZExactZeroIntegerGrid318.uniform]
          · have h' : ¬MvPolynomial.eval
                (ActualTZSignedGridPushforward318.residue (p:=p) L s z) (reduced (p:=p) (D r i))=0 :=
              fun ht=>h (he.mp ht)
            simp [h,h']
        _ ≤ _ := by
          have hc := (NNRat.cast_le (K:=ℝ)).2 H
          have hpow : (((2:ℚ≥0)^n:ℚ≥0):ℝ)=(2:ℝ)^n := by
            simpa only [NNRat.coe_castHom,NNRat.cast_ofNat] using
              (map_pow (NNRat.castHom ℝ) (2:ℚ≥0) n)
          simpa only [NNRat.cast_mul,NNRat.cast_div,NNRat.cast_natCast,hpow] using hc
    have hp0 : (0:ℝ)<p := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p))
    have hM0 : (0:ℝ)<M := by exact_mod_cast hM
    have hmin : 1/((min M p:ℕ):ℝ)≤1/(p:ℝ)+1/M := by
      by_cases h : M≤p
      · rw [min_eq_left h]
        exact le_add_of_nonneg_left (by positivity)
      · rw [min_eq_right (le_of_not_ge h)]
        exact le_add_of_nonneg_right (by positivity)
    calc
      _ ≤ _ := HP
      _ ≤ _ := by
        unfold E
        rw [div_eq_mul_inv]
        have H := mul_le_mul_of_nonneg_left hmin (show 0≤(2:ℝ)^n*(n:ℝ)*(d:ℝ) by positivity)
        simpa only [one_div,mul_assoc] using H
  have H := union_bound m θ hit event (fun _=>by positivity) hθ hθ1 hHit E hE
  simp only [m,E,mul_assoc] at H ⊢
  exact H

end ActualTZGridMarginalJoin318
