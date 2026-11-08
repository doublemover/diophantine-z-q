module
public import KernelUniversalFrame318
public section
noncomputable section
namespace KernelUniversalGeometricBasis318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 KernelUniversalFrame318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ) [NeZero N] (F : Type) [Field F] [IsAlgClosed F]
variable [Algebra (OpenJModel318.Base N) F]
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) F))
variable (s : LiteralIndependentGeometricBases318.Sections N F)
@[expose] def basis := LiteralIndependentGeometricBases318.basisEquiv N F s
lemma restricted_first : restrict N s.val b s.property (first N) = basis N F s 0 := by
  apply Subtype.ext
  rw [restrict_val]
  exact (LiteralIndependentGeometricBases318.first_value N F s).symm
lemma restricted_second : restrict N s.val b s.property (second N) = basis N F s 1 := by
  apply Subtype.ext
  rw [restrict_val]
  exact (LiteralIndependentGeometricBases318.second_value N F s).symm
/-- The exact geometric coordinate map is the inverse linear equivalence of the actual two-point basis. -/
theorem coordinates (c : Fin 2 → ZMod 3) :
    pointEquiv N s.val b s.property (sectionValue N s.val c) = (basis N F s).equivFun.symm c := by
  rw [value_coordinates,combination,map_add,map_smul,map_smul,restricted_first,restricted_second,
    Module.Basis.equivFun_symm_apply,Fin.sum_univ_two]

theorem bijective : Function.Bijective (sectionValue N s.val) := by
  have h : Function.Bijective (fun c => pointEquiv N s.val b s.property (sectionValue N s.val c)) := by
    simpa only [coordinates] using (basis N F s).equivFun.symm.bijective
  exact h.of_comp_left (pointEquiv N s.val b s.property).injective

/-- Every actual geometric base map is covered, with its own specified algebra structure. -/
theorem all_geometric : EtaleSectionTrivialization318.GeometricBijective
    (projection N) (sectionMap N) (section_projection N) := by
  unfold EtaleSectionTrivialization318.GeometricBijective
  intro F _ _ u
  obtain ⟨φ,hφ⟩ := Spec.map_surjective (u ≫ frameBase N)
  letI : Algebra (OpenJModel318.Base N) F := φ.hom.toAlgebra
  have hu : u ≫ frameBase N = Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) F)) := hφ.symm
  exact bijective N F ⟨u,hu⟩
end KernelUniversalGeometricBasis318
