module
public import InertQuadratic318
public import Mathlib.NumberTheory.Padics.PadicIntegers
public section
namespace InertIntegers318
open InertCompletion318 InertPadicEmbedding318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [Fact p.Prime] (nonsquare:¬∃x:ZMod p,x^2=2)

@[expose] def ring : Subring (Field p nonsquare) where
  carrier:={x|‖x‖≤1}
  zero_mem':=by simp
  one_mem':=by simp
  add_mem' {x y} hx hy:= (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  neg_mem' {x} hx:=by simpa using hx
  mul_mem' {x y} hx hy:=by
    change ‖x*y‖≤1
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

@[expose] abbrev Integers := ring p nonsquare

 theorem norm_le_one (x:Integers p nonsquare) : ‖x‖≤1 := x.2

 instance ring_closed : IsClosed (ring p nonsquare:Set (Field p nonsquare)) :=
  isClosed_le continuous_norm continuous_const

 instance integers_complete : CompleteSpace (Integers p nonsquare) :=
  IsClosed.completeSpace_coe

 instance integers_ultrametric : IsUltrametricDist (Integers p nonsquare) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  exact IsUltrametricDist.norm_add_le_max (x:Field p nonsquare) (y:Field p nonsquare)

@[expose] def embedding : Integers p nonsquare →+* Field p nonsquare := (ring p nonsquare).subtype

 theorem embedding_injective : Function.Injective (embedding p nonsquare) := Subtype.val_injective
 theorem embedding_isometry : Isometry (embedding p nonsquare) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  intro x
  rfl

/-- Isometric coefficient inclusion from the actual p-adic integers. -/
@[expose] def padicIntEmbedding : ℤ_[p] →+* Integers p nonsquare :=
  ((padicEmbedding p nonsquare).comp PadicInt.Coe.ringHom).codRestrict (ring p nonsquare) (by
    intro x
    change ‖padicEmbedding p nonsquare (x:ℚ_[p])‖≤1
    rw [padicEmbedding_norm,PadicInt.norm_coe]
    exact PadicInt.norm_le_one x)

 theorem padicIntEmbedding_coe (x:ℤ_[p]) :
    embedding p nonsquare (padicIntEmbedding p nonsquare x)=padicEmbedding p nonsquare (x:ℚ_[p]) := rfl

 theorem padicIntEmbedding_isometry : Isometry (padicIntEmbedding p nonsquare) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  intro x
  change ‖padicEmbedding p nonsquare (x:ℚ_[p])‖=‖x‖
  rw [padicEmbedding_norm,PadicInt.norm_coe]

 theorem padicIntEmbedding_injective : Function.Injective (padicIntEmbedding p nonsquare) :=
  (padicIntEmbedding_isometry p nonsquare).injective

 example : NormedCommRing (Integers p nonsquare) := inferInstance
 example : IsTopologicalRing (Integers p nonsquare) := inferInstance

end
end InertIntegers318
#print axioms InertIntegers318.integers_complete
#print axioms InertIntegers318.integers_ultrametric
#print axioms InertIntegers318.padicIntEmbedding_isometry
