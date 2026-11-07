module
public import InertPadicEmbedding318
public section
namespace InertQuadratic318
open ConcreteG8Domain DiscreteCompletion318 InertCompletion318 InertPadicEmbedding318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [Fact p.Prime] (nonsquare:¬∃x:ZMod p,x^2=2)

/-- The actual coordinates a+b sqrt(2), with Qp coefficients, in the completed field. -/
@[expose] def coordinates : (ℚ_[p]×ℚ_[p]) →+ Field p nonsquare where
  toFun x:=padicEmbedding p nonsquare x.1+embedding p nonsquare i*padicEmbedding p nonsquare x.2
  map_zero':=by simp
  map_add' x y:=by simp only [Prod.fst_add,Prod.snd_add,map_add,mul_add]; abel

 theorem coordinates_rat (a b:ℚ) :
    coordinates p nonsquare ((a:ℚ_[p]),(b:ℚ_[p]))=embedding p nonsquare (pair a b) := by
  have he:pair a b=(a:K)+i*(b:K) := by ext <;> norm_num [pair,i]
  simp [coordinates,he]

 theorem coordinates_continuous : Continuous (coordinates p nonsquare) := by
  have hf:Continuous (padicEmbedding p nonsquare):=(padicEmbedding_uniformContinuous p nonsquare).continuous
  exact (hf.comp continuous_fst).add (continuous_const.mul (hf.comp continuous_snd))

/-- The noncancelling inert norm formula extends to all Qp coefficients. -/
 theorem coordinates_norm (a b:ℚ_[p]) :
    ‖coordinates p nonsquare (a,b)‖=max ‖a‖ ‖b‖ := by
  refine (Padic.denseRange_ratCast p).induction_on₂ ?_ ?_ a b
  · exact isClosed_eq (continuous_norm.comp (coordinates_continuous p nonsquare))
      ((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd))
  · intro a b
    rw [coordinates_rat,norm_pair]

 theorem coordinates_isometry : Isometry (coordinates p nonsquare) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  intro x
  exact coordinates_norm p nonsquare x.1 x.2

/-- Every element of the completion has unique two-dimensional Qp coordinates. -/
 theorem coordinates_surjective : Function.Surjective (coordinates p nonsquare) := by
  have hd:DenseRange (embedding p nonsquare) :=
    embed_dense (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare)
  intro x
  refine hd.induction_on x (coordinates_isometry p nonsquare).isClosedEmbedding.isClosed_range ?_
  intro k
  obtain ⟨a,b⟩:=k
  exact ⟨((a:ℚ_[p]),(b:ℚ_[p])),coordinates_rat p nonsquare a b⟩

@[expose] def coordinateEquiv : (ℚ_[p]×ℚ_[p]) ≃+ Field p nonsquare :=
  AddEquiv.ofBijective (coordinates p nonsquare)
    ⟨(coordinates_isometry p nonsquare).injective,coordinates_surjective p nonsquare⟩

/-- The multiplication is the genuine quadratic multiplication, not just an
additive coordinate equivalence. -/
 theorem coordinates_mul (a b c d:ℚ_[p]) :
    coordinates p nonsquare (a,b)*coordinates p nonsquare (c,d)=
      coordinates p nonsquare (a*c+2*b*d,a*d+b*c) := by
  have hr:=sqrt_two p nonsquare
  simp only [coordinates,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_add,map_mul,map_ofNat]
  linear_combination padicEmbedding p nonsquare b*padicEmbedding p nonsquare d*hr

end
end InertQuadratic318
#print axioms InertQuadratic318.coordinates_norm
#print axioms InertQuadratic318.coordinates_surjective
#print axioms InertQuadratic318.coordinates_mul
