module
public import ComplexProjectiveQuotientTopology318
public import Mathlib.Topology.Separation.Hausdorff
public section
noncomputable section
namespace ComplexProjectiveHermitianProjector318
open Set Topology ComplexConjugate
open ComplexProjectiveQuotientTopology318
variable (ι:Type*) [Fintype ι]
local instance projectiveTopology:TopologicalSpace (Space ι):=topology ι
@[expose] def mass(v:V ι):ℝ:=∑i,Complex.normSq (v i)
lemma mass_pos(v:V ι)(hv:v≠0):0<mass ι v:=by
  classical
  have he:∃j,v j≠0:=by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨j,hj⟩:=he
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hj)
    (Finset.single_le_sum (fun i hi=>Complex.normSq_nonneg _) (Finset.mem_univ j))
lemma mass_smul(a:ℂ)(v:V ι):mass ι (a • v)=Complex.normSq a*mass ι v:=by
  simp only [mass,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,Finset.mul_sum]
lemma mass_continuous:Continuous (mass ι):=by
  unfold mass
  exact continuous_finset_sum _ (fun i hi=>Complex.continuous_normSq.comp (continuous_apply i))

/-- The genuine normalized Hermitian rank-one projector of a complex
line. It is invariant under EVERY nonzero complex scalar, not just phase. -/
@[expose] def vectorProjector(v:V ι):ι→ι→ℂ:=fun i j=>
  v i*conj (v j)/(mass ι v:ℂ)
lemma vectorProjector_smul(a:ℂ)(ha:a≠0)(v:V ι)(hv:v≠0):
    vectorProjector ι (a • v)=vectorProjector ι v:=by
  funext i j
  simp only [vectorProjector,Pi.smul_apply,smul_eq_mul,map_mul,mass_smul,Complex.ofReal_mul]
  have hna:(Complex.normSq a:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Complex.normSq_pos.mpr ha))
  have hnv:(mass ι v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt (mass_pos ι v hv))
  rw [show a*v i*(conj a*conj (v j))=(a*conj a)*(v i*conj (v j)) by ring,
    Complex.mul_conj]
  field_simp [hna,hnv]
@[expose] def projector:Space ι→(ι→ι→ℂ):=
  Projectivization.lift (fun v:NonzeroVectors ι=>vectorProjector ι v.val)
    (by
      intro v w a he
      have ha:a≠0:=by
        intro h
        apply v.property
        simpa only [h,zero_smul] using he
      rw [he]
      exact vectorProjector_smul ι a ha w.val w.property)
@[simp] lemma projector_mk(v:V ι)(hv:v≠0):
    projector ι (Projectivization.mk ℂ v hv)=vectorProjector ι v:=rfl
lemma continuous_projector:Continuous (projector ι):=by
  apply (quotientMap ι).continuous_iff.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((continuous_apply i).comp continuous_subtype_val).mul
    (Complex.continuous_conj.comp ((continuous_apply j).comp continuous_subtype_val))).div
    (Complex.continuous_ofReal.comp ((mass_continuous ι).comp continuous_subtype_val))
    (fun v=>Complex.ofReal_ne_zero.mpr (ne_of_gt (mass_pos ι v.val v.property)))

lemma ratio_from_projector(v:V ι)(hv:v≠0)(j:ι)(hj:v j≠0)(i:ι):
    vectorProjector ι v i j/vectorProjector ι v j j=v i/v j:=by
  have hm:(mass ι v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt (mass_pos ι v hv))
  have hc:conj (v j)≠0:=by simpa using hj
  simp only [vectorProjector]
  field_simp [hm,hj,hc]
  <;> ring
lemma diagonal_ne_zero(v:V ι)(hv:v≠0)(j:ι):
    vectorProjector ι v j j≠0↔v j≠0:=by
  simp only [vectorProjector,div_ne_zero_iff,mul_ne_zero_iff,
    Complex.ofReal_ne_zero,ne_of_gt (mass_pos ι v hv),and_true]
  constructor
  · exact fun h=>h.1
  · intro h
    exact ⟨h,by simpa using h⟩

/-- Normalized Hermitian projectors distinguish actual projective lines.
This is a target-topology fact, not injectivity of the four-theta map. -/
lemma projector_injective:Function.Injective (projector ι):=by
  intro p q hpq
  classical
  let v:=Projectivization.rep p
  let w:=Projectivization.rep q
  have hv:v≠0:=Projectivization.rep_nonzero p
  have hw:w≠0:=Projectivization.rep_nonzero q
  have he:∃j,w j≠0:=by
    by_contra h
    push_neg at h
    exact hw (funext h)
  obtain ⟨j,hj⟩:=he
  have hp:vectorProjector ι v=vectorProjector ι w:=by
    simpa only [v,w,←projector_mk,Projectivization.mk_rep] using hpq
  have hjv:v j≠0:=(diagonal_ne_zero ι v hv j).mp (by
    rw [hp];exact (diagonal_ne_zero ι w hw j).mpr hj)
  have hr:∀i,v i/v j=w i/w j:=by
    intro i
    rw [←ratio_from_projector ι v hv j hjv i,hp,ratio_from_projector ι w hw j hj i]
  have hline:Projectivization.mk ℂ v hv=Projectivization.mk ℂ w hw:=by
    apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr
    refine ⟨v j/w j,?_⟩
    funext i
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _=(w i/w j)*v j:=by ring
      _=(v i/v j)*v j:=by rw [hr i]
      _=v i:=div_mul_cancel₀ _ hjv
  simpa only [v,w,Projectivization.mk_rep] using hline

theorem hausdorff:T2Space (Space ι):=
  T2Space.of_injective_continuous (projector_injective ι) (continuous_projector ι)
end ComplexProjectiveHermitianProjector318
