module
public import MarkedPeriod318
public import Mathlib.Algebra.BigOperators.Associated
public section
noncomputable section
namespace PrimitiveMarkingLift318
open PrimitiveTorsion318 ModularTorsionTransport318 MarkedPeriod318
open scoped MatrixGroups

/-- The explicit primitive lift uses no surjectivity assertion for SL₂ mod N.
Keep A=y+N>0 and choose B=x+N·C with one squarefree correction C.
At every prime dividing A the correction either kills itself mod p (p∤x)
or is a unit and also p∤N (p|x). -/
theorem lift (N : ℕ) [NeZero N] (x : ZMod N × ZMod N) (h : Primitive N x) :
    ∃A B : ℕ,A.Coprime B ∧ (A:ZMod N)=x.2 ∧ (B:ZMod N)=x.1 := by
  classical
  let A := x.2.val+N
  let P := A.primeFactors.filter (fun p => ¬p∣x.1.val)
  let C := ∏p∈P,p
  let B := x.1.val+N*C
  have ha : 0<A := by dsimp [A];have := NeZero.pos N;omega
  have hab : A.Coprime B := by
    by_contra hn
    obtain ⟨p,hp,hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hpA : p∈A.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpa,ha.ne'⟩
    by_cases hx:p∣x.1.val
    · have hN : ¬p∣N := by
        intro hd
        have hy : p∣x.2.val := (Nat.dvd_add_iff_left hd).mpr hpa
        have h1 := Nat.dvd_gcd hd (Nat.dvd_gcd hx hy)
        rw [show Nat.gcd N (Nat.gcd x.1.val x.2.val)=1 from h] at h1
        exact hp.ne_one (Nat.dvd_one.mp h1)
      have hnC : ¬p∣C := by
        intro hC
        obtain ⟨q,hq,hd⟩ := (hp.prime.dvd_finsetProd_iff id).mp hC
        have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
        have he : p=q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
        exact (Finset.mem_filter.mp hq).2 (he ▸ hx)
      exact (hp.dvd_mul.mp ((Nat.dvd_add_iff_right hx).mpr hpb)).elim hN hnC
    · have hC : p∣C := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hpA,hx⟩)
      exact hx ((Nat.dvd_add_iff_left (dvd_mul_of_dvd_right hC N)).mpr hpb)
  exact ⟨A,B,hab,by simp [A],by simp [B]⟩

/-- Every primitive marking (x,y) is literally an integral matrix transport
of (0,1) in the project's inverse-transpose convention. -/
theorem transitive (N : ℕ) [NeZero N] (x : ZMod N × ZMod N) (h : Primitive N x) :
    ∃g:SL(2,ℤ), residueMap g N (standardLabel N)=x := by
  obtain ⟨A,B,hAB,hA,hB⟩ := lift N x h
  have hb := Nat.gcd_eq_gcd_ab A B
  rw [hAB.gcd_eq_one] at hb
  let g : SL(2,ℤ) :=
    ⟨!![(A:ℤ),Nat.gcdB A B;-(B:ℤ),Nat.gcdA A B],by
      have hdet : (A:ℤ)*Nat.gcdA A B - Nat.gcdB A B*(-(B:ℤ))=1 := by
        norm_num only [Nat.cast_one] at hb
        nlinarith [hb]
      simpa [Matrix.det_fin_two] using hdet⟩
  refine ⟨g,?_⟩
  apply Prod.ext <;> simp [residueMap,standardLabel,g,hA,hB]
end PrimitiveMarkingLift318
