module
public import ActualA4IntegerBoxFibres318
public section
noncomputable section
namespace ActualA4CRTResidueProduct318
open Classical
open scoped BigOperators
open ActualA4IntegerBoxFibres318

/-- One CRT for each coordinate. This is an exact pair of residue masks
on the same four integer coordinates, not independence of Gaussian primes. -/
def vecCRT {l d : ℕ} (h : Nat.Coprime l d) :
    Vec (ZMod (l*d)) ≃ Vec (ZMod l) × Vec (ZMod d) where
  toFun x := (fun i => (ZMod.chineseRemainder h (x i)).1,
              fun i => (ZMod.chineseRemainder h (x i)).2)
  invFun y i := (ZMod.chineseRemainder h).symm (y.1 i,y.2 i)
  left_inv x := by
    funext i
    exact (ZMod.chineseRemainder h).symm_apply_apply (x i)
  right_inv y := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((ZMod.chineseRemainder h).apply_symm_apply (y.1 i,y.2 i))
    · exact congrArg Prod.snd ((ZMod.chineseRemainder h).apply_symm_apply (y.1 i,y.2 i))

@[expose] def joint {l d : ℕ} (h : Nat.Coprime l d)
    (Ω : Finset (Vec (ZMod l))) (D : Finset (Vec (ZMod d))) :
    Finset (Vec (ZMod (l*d))) :=
  (Ω.product D).map (vecCRT h).symm.toEmbedding

theorem joint_card {l d : ℕ} (h : Nat.Coprime l d)
    (Ω : Finset (Vec (ZMod l))) (D : Finset (Vec (ZMod d))) :
    (joint h Ω D).card=Ω.card*D.card := by
  rw [joint,Finset.card_map,Finset.product_eq_sprod]
  exact Finset.card_product Ω D

theorem residue_crt {l d : ℕ} (h : Nat.Coprime l d) (B : ℕ) (x : Vec (Digit B)) :
    vecCRT h (residue (l*d) B x)=(residue l B x,residue d B x) := by
  apply Prod.ext <;> funext i
  · exact congrArg Prod.fst (map_intCast (ZMod.chineseRemainder h).toRingHom (coordinate B (x i)))
  · exact congrArg Prod.snd (map_intCast (ZMod.chineseRemainder h).toRingHom (coordinate B (x i)))

theorem mem_joint_iff {l d : ℕ} (h : Nat.Coprime l d)
    (Ω : Finset (Vec (ZMod l))) (D : Finset (Vec (ZMod d))) (B : ℕ) (x : Vec (Digit B)) :
    x ∈ accepted (l*d) B (joint h Ω D) ↔ residue l B x ∈ Ω ∧ residue d B x ∈ D := by
  change x ∈ (Finset.univ : Finset (Vec (Digit B))).filter (fun q => residue (l*d) B q ∈ joint h Ω D) ↔ _
  rw [Finset.mem_filter]
  rw [and_iff_right (Finset.mem_univ x)]
  rw [joint,Finset.product_eq_sprod]
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hx
    have hVal : (vecCRT h).symm y = residue (l*d) B x := he
    have hY : y=(residue l B x,residue d B x) := by rw [←residue_crt h B x,←hVal,Equiv.apply_symm_apply]
    rw [hY] at hy
    exact Finset.mem_product.mp hy
  · intro hx
    refine Finset.mem_map.mpr ⟨(residue l B x,residue d B x),Finset.mem_product.mpr hx,?_⟩
    change (vecCRT h).symm (residue l B x,residue d B x)=_
    rw [←residue_crt h B x,Equiv.symm_apply_apply]

end ActualA4CRTResidueProduct318
