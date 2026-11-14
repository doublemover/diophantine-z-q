module
public import PELOriginalQuadraticMultiplication318
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public section
noncomputable section
namespace PELOriginalQuadraticRelationDimension318
open PELOriginalQuadraticMultiplication318 PELOriginalCubicRelationIdeal318
open PELOriginalLevelTheta318 QuadraticMonomialCoordinates318
lemma input_card:Fintype.card Quad=45:=by
  rw [Sym.card_sym_eq_choose,PELOriginalLevelTheta318.label_card]
  norm_num
lemma input_dimension:Module.finrank ℂ Coefficients=45:=by
  simpa [Module.finrank_pi] using input_card
lemma output_dimension:Module.finrank ℂ (Label 6→ℂ)=36:=by
  simp [Module.finrank_pi,Label,Fintype.card_prod]
variable (τ:ℂ)(hτ:0<τ.im)
/-- Rank-nullity for the ACTUAL multiplication matrix. Only rank≤36 is
used. No surjectivity, exact rank36, or normal generation is asserted. -/
theorem kernel_dimension_lower_bound:
    9≤Module.finrank ℂ (LinearMap.ker (matrixMap τ hτ)):=by
  have h:=LinearMap.finrank_range_add_finrank_ker (matrixMap τ hτ)
  have hr:Module.finrank ℂ (LinearMap.range (matrixMap τ hτ))≤36:=by
    simpa only [output_dimension] using (LinearMap.range (matrixMap τ hτ)).finrank_le
  rw [input_dimension] at h
  omega
/-- Actual kernel vectors become genuine polynomial relations by the
INJECTIVE unordered-monomial coordinate map. -/
@[expose] def equationMap:LinearMap.ker (matrixMap τ hτ)→ₗ[ℂ]Equations:=
  (polynomial (Label 3)).comp (LinearMap.ker (matrixMap τ hτ)).subtype
lemma equationMap_injective:Function.Injective (equationMap τ hτ):=
  (polynomial_injective (Label 3)).comp Subtype.coe_injective
@[expose] def actualQuadrics:Submodule ℂ Equations:=LinearMap.range (equationMap τ hτ)
theorem actual_relation(p:Equations)(hp:p∈actualQuadrics τ hτ):p∈relations τ hτ:=by
  obtain ⟨c,rfl⟩:=hp
  exact (kernel_iff_relation τ hτ c.val).mp c.property
theorem actual_homogeneous(p:Equations)(hp:p∈actualQuadrics τ hτ):p.IsHomogeneous 2:=by
  obtain ⟨c,rfl⟩:=hp
  exact homogeneous (Label 3) c.val
theorem actual_quadrics_iff(p:Equations):
    p∈actualQuadrics τ hτ↔p.IsHomogeneous 2 ∧ p∈relations τ hτ:=by
  constructor
  · intro hp
    exact ⟨actual_homogeneous τ hτ p hp,actual_relation τ hτ p hp⟩
  · rintro ⟨hh,hr⟩
    let c:Coefficients:=fun a=>p.coeff (exponent (Label 3) a)
    have hc:polynomial (Label 3) c=p:=all_quadratics (Label 3) p hh
    have hk:matrixMap τ hτ c=0:=(kernel_iff_relation τ hτ c).mpr (hc.symm ▸ hr)
    exact ⟨⟨c,hk⟩,hc⟩
/-- At least NINE linearly independent ACTUAL quadratic equations in
the same nine cubic theta coordinates. This is a dimension LOWER BOUND,
not a list of full ideal generators or an image-equality theorem. -/
theorem actual_quadrics_dimension:
    9≤Module.finrank ℂ (actualQuadrics τ hτ):=by
  rw [actualQuadrics,LinearMap.finrank_range_of_inj (equationMap_injective τ hτ)]
  exact kernel_dimension_lower_bound τ hτ
end PELOriginalQuadraticRelationDimension318
