module
public import FiberCentralizer318
public import Mathlib.FieldTheory.Normal.Closure

@[expose] public section
noncomputable section

namespace OriginalFineFibreNormalResidue318
universe u v w z
variable {B : Type u} [CommRing B] [Algebra ℚ B]
variable {L : Type v} [Field L] [Algebra ℚ L]
variable {Ω : Type w} [Field Ω] [Algebra ℚ Ω]
variable {G : Type z} [Group G]
variable (δ : G →* (B ≃ₐ[ℚ] B)) (p : B →ₐ[ℚ] L) (ι : L →ₐ[ℚ] Ω)

/-- This is the original read of the closed fine point, composed
with the exact scheme deck arrow in the contravariant convention. -/
def residueOrbit (g : G) : B →ₐ[ℚ] L :=
  p.comp (δ g⁻¹).toAlgHom

/-- Geometric points that are actually defined by a map into this
SAME closed residue field, with one fixed embedding. -/
def baseChangePoint (s : B →ₐ[ℚ] L) : B →ₐ[ℚ] Ω :=
  ι.comp s

theorem baseChangePoint_injective : Function.Injective (baseChangePoint (B:=B) ι) := by
  intro a b h
  apply AlgHom.ext
  intro x
  exact ι.injective (DFunLike.congr_fun h x)

variable (orbit : Function.Bijective (fun g => baseChangePoint ι (residueOrbit δ p g)))

include orbit in
/-- The true geometric cover splits over a *single* retained residue
field, not a newly adjoined normal closure. Every witness here is an
actual B-valued point map, in the same original deck orbit. -/
theorem baseChangePoint_surjective : Function.Surjective (baseChangePoint (B:=B) ι) := by
  intro s
  obtain ⟨g,hg⟩ := orbit.2 s
  exact ⟨residueOrbit δ p g,hg⟩

include orbit in
theorem residueOrbit_bijective : Function.Bijective (residueOrbit δ p) := by
  constructor
  · intro a b hab
    exact orbit.1 (congrArg (baseChangePoint ι) hab)
  · intro s
    obtain ⟨g,hg⟩ := orbit.2 (baseChangePoint ι s)
    exact ⟨g,baseChangePoint_injective ι hg⟩

/-- The base-change maps are genuinely inverse as point sets over
the fixed embedding; they do not just certify equality of cardinalities. -/
def pointEquivalence : (B →ₐ[ℚ] L) ≃ (B →ₐ[ℚ] Ω) :=
  Equiv.ofBijective (baseChangePoint ι)
    ⟨baseChangePoint_injective ι,baseChangePoint_surjective δ p ι orbit⟩

variable [Normal ℚ Ω]

include orbit in
/-- Every conjugate of the residue field is already in it: lift a
field element to its actual affine fibre algebra, then use a deck
translate of the SAME selected point. -/
theorem residueNormal (closed : Function.Surjective p) : Normal ℚ L := by
  let K := ι.fieldRange
  let e : L ≃ₐ[ℚ] K := ι.equivFieldRange
  letI : Normal ℚ K := (IntermediateField.normal_iff_forall_fieldRange_le (K:=K)).2 (by
    intro σ z hz
    obtain ⟨c,rfl⟩ := AlgHom.mem_fieldRange.mp hz
    obtain ⟨a,ha⟩ := closed (e.symm c)
    have he : e (p a)=c := by rw [ha,e.apply_symm_apply]
    obtain ⟨g,hg⟩ := orbit.2 (σ.comp (e.toAlgHom.comp p))
    refine AlgHom.mem_fieldRange.mpr ⟨residueOrbit δ p g a,?_⟩
    have h := DFunLike.congr_fun hg a
    change ι (residueOrbit δ p g a)=σ (e (p a)) at h
    exact h.trans (congrArg σ he))
  exact Normal.of_algEquiv e.symm

variable [FiniteDimensional ℚ L]

include orbit in
theorem residueGalois (closed : Function.Surjective p) : IsGalois ℚ L :=
  isGalois_iff.mpr ⟨inferInstance,residueNormal δ p ι orbit closed⟩

/-- The actual deck action on point coordinates precomposes inverse
arrows. Omitting the inverse would give an opposite action. -/
def deck : G →* Equiv.Perm (B →ₐ[ℚ] L) where
  toFun g :=
    { toFun := fun q => q.comp (δ g⁻¹).toAlgHom
      invFun := fun q => q.comp (δ g).toAlgHom
      left_inv := by
        intro q
        apply AlgHom.ext
        intro a
        change q ((δ g⁻¹) ((δ g) a))=q a
        simp only [←AlgEquiv.mul_apply,←map_mul,inv_mul_cancel,map_one,AlgEquiv.one_apply]
      right_inv := by
        intro q
        apply AlgHom.ext
        intro a
        change q ((δ g) ((δ g⁻¹) a))=q a
        simp only [←AlgEquiv.mul_apply,←map_mul,mul_inv_cancel,map_one,AlgEquiv.one_apply] }
  map_one' := by
    apply Equiv.ext
    intro q
    apply AlgHom.ext
    intro a
    change q ((δ (1:G)⁻¹) a)=q a
    simp only [inv_one,map_one,AlgEquiv.one_apply]
  map_mul' g h := by
    apply Equiv.ext
    intro q
    apply AlgHom.ext
    intro a
    change q ((δ (g*h)⁻¹) a)=q ((δ h⁻¹) ((δ g⁻¹) a))
    rw [mul_inv_rev,map_mul,AlgEquiv.mul_apply]

/-- Coefficient Galois postsamples points, hence commutes with the
scheme deck action. The same affine evaluation witnesses faithfulness. -/
def gal : (L ≃ₐ[ℚ] L) →* Equiv.Perm (B →ₐ[ℚ] L) where
  toFun σ :=
    { toFun := fun q => σ.toAlgHom.comp q
      invFun := fun q => σ.symm.toAlgHom.comp q
      left_inv := by
        intro q
        apply AlgHom.ext
        intro a
        exact σ.symm_apply_apply (q a)
      right_inv := by
        intro q
        apply AlgHom.ext
        intro a
        exact σ.apply_symm_apply (q a) }
  map_one' := by
    apply Equiv.ext
    intro q
    apply AlgHom.ext
    intro a
    rfl
  map_mul' _ _ := by
    apply Equiv.ext
    intro q
    apply AlgHom.ext
    intro a
    rfl

theorem commute (σ : L ≃ₐ[ℚ] L) (g : G) (q : B →ₐ[ℚ] L) :
    gal σ (deck δ g q)=deck δ g (gal σ q) :=
  AlgHom.ext (fun _ => rfl)

theorem gal_faithful (closed : Function.Surjective p) :
    Function.Injective (gal (B:=B) (L:=L)) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  obtain ⟨a,rfl⟩ := closed x
  exact DFunLike.congr_fun (DFunLike.congr_fun h p) a

include orbit in
/-- On the actual affine original level-three fibre, the retained
closed point already has a normal field of degree dividing 576.
No normal extension chosen independently of this point is admitted. -/
theorem degree576 (closed : Function.Surjective p) (hG : Nat.card G=576) :
    Module.finrank ℚ L ∣ 576 ∧ Module.finrank ℚ L≤576 := by
  letI : IsGalois ℚ L := residueGalois δ p ι orbit closed
  exact FiberCentralizer318.galois_torsor_degree_576 L (deck δ) p
    (residueOrbit_bijective δ p ι orbit) hG gal (commute δ) (gal_faithful p closed)

end OriginalFineFibreNormalResidue318

#print axioms OriginalFineFibreNormalResidue318.pointEquivalence
#print axioms OriginalFineFibreNormalResidue318.residueNormal
#print axioms OriginalFineFibreNormalResidue318.gal_faithful
#print axioms OriginalFineFibreNormalResidue318.degree576
