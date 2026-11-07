module
public import FiniteHeightEquiv
public section
noncomputable section
open NumberField Height
namespace RelativeHeightEquiv
set_option maxHeartbeats 0
variable {F G : Type*} [Field F] [Field G] [NumberField F] [NumberField G]

lemma infinite_part_embeddings (x : F) :
    (∏ w : InfinitePlace F, max (w x) 1 ^ w.mult) =
      ∏ φ : F →+* ℂ, max ‖φ x‖ 1 := by
  classical
  rw [←Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => max ‖φ x‖ 1)]
  have h (w : InfinitePlace F) (φ) (hφ : φ ∈ ({φ | InfinitePlace.mk φ=w} : Finset _)) :
      max ‖φ x‖ 1 = max (w x) 1 := by
    rw [←(Finset.mem_filter.mp hφ).2,InfinitePlace.apply]
  simp_rw [Finset.prod_congr rfl (h _),Finset.prod_const,InfinitePlace.card_filter_mk_eq]

def embeddingEquiv (e : F ≃+* G) : (G →+* ℂ) ≃ (F →+* ℂ) where
  toFun φ := φ.comp e.toRingHom
  invFun φ := φ.comp e.symm.toRingHom
  left_inv φ := by ext x; simp
  right_inv φ := by ext x; simp

lemma infinite_part_equiv (e : F ≃+* G) (x : F) :
    (∏ w : InfinitePlace G, max (w (e x)) 1 ^ w.mult) =
      ∏ v : InfinitePlace F, max (v x) 1 ^ v.mult := by
  rw [infinite_part_embeddings,infinite_part_embeddings]
  exact Fintype.prod_equiv (embeddingEquiv e) _ _ (fun _ => rfl)

lemma mulHeight_equiv (e : F ≃+* G) (x : F) :
    Height.mulHeight₁ (e x)=Height.mulHeight₁ x := by
  rw [NumberField.mulHeight₁_eq,NumberField.mulHeight₁_eq,
    infinite_part_equiv,FiniteHeightEquiv.finite_part_equiv]

#print axioms infinite_part_embeddings
#print axioms embeddingEquiv
#print axioms infinite_part_equiv
#print axioms mulHeight_equiv
end RelativeHeightEquiv
