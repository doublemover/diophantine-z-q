module
public import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section

namespace CTClosedGaloisCocycleFiniteLayer318

open Set Filter
open scoped Topology

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "G" => (A ≃ₐ[K] A)

abbrev FL := FiniteGaloisIntermediateField K A
abbrev restriction (L : FL K) : G →* (L.toIntermediateField ≃ₐ[K] L.toIntermediateField) :=
  AlgEquiv.restrictNormalHom (F := K) (K₁ := A) L.toIntermediateField

/-- A locally constant crossed homomorphism on a closed subgroup
factors through that subgroup's *actual image* on one finite normal
field. The same field contains every literal unit value. This does
not require the subgroup to be open or the cocycle to extend to G. -/
theorem finite_layer_for_closed_cocycle (I : Subgroup G) (hClosed : IsClosed (I : Set G))
    (c : I → Aˣ) (hlc : IsLocallyConstant c)
    (hc : ∀ g h : I, c (g*h)=(g : G) • c h*c g) :
    ∃ L : FL K,
      (∀ g h : I, restriction K L (g : G)=restriction K L (h : G) → c g=c h) ∧
      ∀ g, (c g : A) ∈ L.toIntermediateField := by
  letI : CompactSpace I := isCompact_iff_compactSpace.mp hClosed.isCompact
  have hOne : c 1=1 := by
    have h := hc 1 1
    simp only [one_mul,Subgroup.coe_one,one_smul] at h
    apply mul_left_cancel (a := c 1)
    exact h.symm.trans (mul_one _).symm
  obtain ⟨O,hO,h₁,hCO⟩ := hlc.exists_open (1:I)
  obtain ⟨U,hU,hpre⟩ := isOpen_induced_iff.mp hO
  have hU₁ : (1:G)∈U := by
    have h : (1:I)∈((↑) : I → G) ⁻¹' U := hpre.symm ▸ h₁
    exact h
  let X := Set.range (fun i : I => (c i : A))
  have hX : X.Finite := (hlc.comp (fun x : Aˣ => (x:A))).range_finite
  letI : Finite X := finite_coe_iff.mpr hX
  let V : Set G := ⋂ x : X, (MulAction.stabilizer G x.val : Set G)
  have hV : V∈𝓝 (1:G) := by
    apply Filter.iInter_mem.2
    intro x
    exact (stabilizer_isOpen_of_isIntegral x.val).mem_nhds
      (MulAction.stabilizer G x.val).one_mem
  obtain ⟨L,hL⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (U ∩ V)).1
    (inter_mem (hU.mem_nhds hU₁) hV)
  refine ⟨L,?_,?_⟩
  · intro g h he
    let z : I := g⁻¹*h
    have hz : (z : G)∈L.toIntermediateField.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      change restriction K L ((g : G)⁻¹*(h : G))=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hZ : z∈O := by
      rw [← hpre]
      exact (hL hz).1
    have hcz : c z=1 := (hCO z hZ).trans hOne
    have hgz : g*z=h := by simp only [z,mul_inv_cancel_left]
    have hc' := hc g z
    rw [hgz,hcz,smul_one,one_mul] at hc'
    exact hc'.symm
  · intro g
    let x : X := ⟨(c g : A),⟨g,rfl⟩⟩
    change x.val∈L.toIntermediateField
    rw [← InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField,
      IntermediateField.mem_fixedField_iff]
    intro s hs
    exact Set.mem_iInter.1 (hL hs).2 x

end CTClosedGaloisCocycleFiniteLayer318
