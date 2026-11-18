module
public import PrimitiveMarkingLift318
public import ActualGammaHIndexUpper318
public section
noncomputable section
namespace ActualPrimitiveMarkingClassCount318
open scoped MatrixGroups
open MarkedPeriod318 ModularTorsionTransport318 PrimitiveTorsion318 EllipticTorsion318
open GammaHGroup318
abbrev Points (z:UpperHalfPlane) (N:ℕ) := {P : (ModularWeierstrass318.curve z).toAffine.Point // addOrderOf P=N}

def relabel (z:UpperHalfPlane) (N:ℕ) [NeZero N] (g:SL(2,ℤ)) : Points z N :=
  primitiveEquiv z N
    ⟨residueMap g N (standardLabel N),(primitive_iff g N z _).mpr
      ((point_order_eq_iff z N _).mp (standardPoint_order N z))⟩

/-- All exact-order points on the genuine elliptic curve of a chosen
parameter, not just their unordered cyclic subgroups. -/
theorem relabel_onto (z:UpperHalfPlane) (N:ℕ) [NeZero N] : Function.Surjective (relabel z N) := by
  intro p
  let v := (primitiveEquiv z N).symm p
  obtain ⟨g,hg⟩ := PrimitiveMarkingLift318.transitive N v.val v.property
  refine ⟨g,?_⟩
  apply (primitiveEquiv z N).symm.injective
  change (primitiveEquiv z N).symm (primitiveEquiv z N _) = v
  rw [Equiv.symm_apply_apply]
  exact Subtype.ext hg

/-- Right multiplication by a literal element of Γ_H scales the relabelled
point by the actual upper-left unit in H. The lower-right convention gives
the inverse unit; replacing H by its elements' inverses does not change H. -/
theorem relabel_right (z:UpperHalfPlane) (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (g:SL(2,ℤ)) (k:gammaH N H) :
    ∃u:H,(relabel z N (g*k.val)).val=(u.val:ZMod N).val • (relabel z N g).val := by
  obtain ⟨hc,u,hu⟩ := (MarkedDiamond318.preservesOrbit_iff N H k.val).mp
    ((mem_iff_markedOrbit N H k.val).mp k.property)
  refine ⟨u,?_⟩
  change torsionMap z N (residueMap (g*k.val) N (standardLabel N))=_ • torsionMap z N _
  rw [←map_nsmul]
  congr 1
  apply Prod.ext <;>
    simp [residueMap,standardLabel,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,
      Fin.sum_univ_two,Prod.smul_fst,Prod.smul_snd,nsmul_eq_mul,hc,hu] <;> ring

/-- Any actual geometric marking-class set on this elliptic curve receives a
surjective map from its exact-order-N points respecting the H diamond
multiplications. The standard coset quotient therefore covers it, with no
assumption on the order of the curve's automorphisms. This proves the
required bound for a moduli fibre directly from the point-classification
property, independently of a scheme-to-analytic fibre injection. -/
theorem classes {Y:Type*} (z:UpperHalfPlane) (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (forget:Points z N→Y) (onto:Function.Surjective forget)
    (diamond:∀(u:H) (P Q:Points z N),P.val=(u.val:ZMod N).val • Q.val → forget P=forget Q) :
    Finite Y ∧ Nat.card Y≤(gammaH N H).index := by
  classical
  let Γ := gammaH N H
  letI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le (gamma1_le_gammaH N H)
  letI : Fintype (SL(2,ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  let f (q:SL(2,ℤ) ⧸ Γ) := forget (relabel z N q.out)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨P,hP⟩ := onto y
    obtain ⟨g,hg⟩ := relabel_onto z N P
    let q:SL(2,ℤ) ⧸ Γ := ⟦g⟧
    have hq : (⟦q.out⟧:SL(2,ℤ) ⧸ Γ)=⟦g⟧ := q.out_eq
    let k : Γ := ⟨q.out⁻¹*g,QuotientGroup.leftRel_apply.mp (Quotient.exact hq)⟩
    obtain ⟨u,hu⟩ := relabel_right z N H q.out k
    have he : q.out*k.val=g := by dsimp [k];group
    rw [he,hg] at hu
    exact ⟨q,(diamond u P (relabel z N q.out) hu).symm.trans hP⟩
  exact ⟨Finite.of_surjective f hf,Nat.card_le_card_of_surjective f hf⟩
end ActualPrimitiveMarkingClassCount318
