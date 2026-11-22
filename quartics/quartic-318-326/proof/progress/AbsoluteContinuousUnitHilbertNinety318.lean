module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section
namespace AbsoluteContinuousUnitHilbertNinety318

open scoped Topology
open groupCohomology

variable {F M : Type*} [Field F] [Field M] [Algebra F M] [IsGalois F M]
local notation "G" => (M ≃ₐ[F] M)

/-- Continuous Hilbert 90 for all closure units, not merely scalar
quadratic characters. A finite NORMAL fixing subgroup N in the unit
fiber makes the crossed cocycle constant on right cosets. Normality in
turn forces N to fix the values, so the finite cochain is valued in the
same finite field cut out by N: no unjustified descent of coefficients. -/
theorem continuous_hilbert90 (f : G → Mˣ) (lc : IsLocallyConstant f)
    (coc : ∀ g h : G, (f (g*h) : M)=g (f h : M)*(f g : M)) :
    ∃ u : Mˣ, ∀ g : G, (f g : M)=g (u:M)/(u:M) := by
  classical
  have h1 : f 1=1 := by
    apply Units.ext
    have h := coc 1 1
    change (f (1*1) : M)=(f 1 : M)*(f 1 : M) at h
    rw [one_mul] at h
    exact (mul_right_cancel₀ (f 1).ne_zero ((one_mul (f 1 : M)).trans h)).symm
  have nb : {g : G | f g=1} ∈ 𝓝 (1:G) := (lc.isOpen_fiber 1).mem_nhds h1
  obtain ⟨K,hK,hN,hsub⟩ := (krullTopology_mem_nhds_one_iff_of_normal F M _).mp nb
  let := hK
  let := hN
  let res : G →* (K ≃ₐ[F] K) := AlgEquiv.restrictNormalHom K
  have rs : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective M
  have ker : ∀ z : G, res z=1 → f z=1 := by
    intro z hz
    apply hsub
    rw [←K.restrictNormalHom_ker]
    exact hz
  have desc (g h : G) (eq : res g=res h) : f g=f h := by
    let z := h⁻¹*g
    have hz : res z=1 := by simp [z,eq]
    have hgz : h*z=g := by simp [z]
    have hh := coc h z
    rw [hgz,ker z hz,Units.val_one,map_one,one_mul] at hh
    exact Units.ext hh
  have fv (g : G) : (f g : M)∈K := by
    rw [←InfiniteGalois.fixedField_fixingSubgroup K,IntermediateField.mem_fixedField_iff]
    intro z hz
    have hz' : res z=1 := by
      change z∈(AlgEquiv.restrictNormalHom K : G →* _).ker
      rwa [K.restrictNormalHom_ker]
    have eq := desc (z*g) g (by rw [map_mul,hz',one_mul])
    have hh := coc z g
    rw [eq,ker z hz',Units.val_one,mul_one] at hh
    exact hh.symm
  let lift (a : K ≃ₐ[F] K) := Classical.choose (rs a)
  have hl (a : K ≃ₐ[F] K) : res (lift a)=a := Classical.choose_spec (rs a)
  let coeff (g : G) : K := ⟨(f g : M),fv g⟩
  have cn (g : G) : coeff g ≠ 0 := by
    intro he
    exact (f g).ne_zero (congrArg (fun z:K => (z:M)) he)
  let w (a : K ≃ₐ[F] K) : Kˣ := Units.mk0 (coeff (lift a)) (cn _)
  have cw (g : G) : ((w (res g) : K) : M)=(f g:M) :=
    congrArg (fun z : Mˣ => (z:M)) (desc (lift (res g)) g (hl _))
  have wc : IsMulCocycle₁ w := by
    intro a b
    obtain ⟨g,rfl⟩ := rs a
    obtain ⟨h,rfl⟩ := rs b
    apply Units.ext
    apply Subtype.ext
    change ((w (res g * res h) : K) : M) =
      ((res g (w (res h) : K) : K) : M)*((w (res g) : K) : M)
    rw [←res.map_mul,cw]
    change _=((g.restrictNormal K (w (res h) : K):K):M)*_
    have nrm : ((g.restrictNormal K (w (res h):K):K):M)=g ((w (res h):K):M) :=
      g.restrictNormal_commutes K (w (res h):K)
    rw [nrm,cw,cw]
    exact coc g h
  obtain ⟨b,hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units w wc
  let u : Mˣ := Units.map (algebraMap K M).toMonoidHom b
  refine ⟨u,?_⟩
  intro g
  have hh := congrArg (fun z : Kˣ => (z:K)) (hb (res g))
  have hx : (res g (b:K))/(b:K) = (w (res g):K) := by
    simpa only [AlgEquiv.smul_units_def,Units.val_div_eq_div_val,Units.coe_map,MonoidHom.coe_ofClass] using hh
  have hm := congrArg (algebraMap K M) hx
  rw [map_div₀] at hm
  have nrm : (algebraMap K M) (res g (b:K))=g ((b:K):M) :=
    g.restrictNormal_commutes K (b:K)
  rw [nrm] at hm
  exact (cw g).symm.trans hm.symm

end AbsoluteContinuousUnitHilbertNinety318
