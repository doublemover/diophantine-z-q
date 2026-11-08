/-- The sole geometric interface retained here. This is the actual five-contact
height on primitive rational homogeneous coordinates, with the literal bad-prime
product and finite odd-contact radical. It is not asserted as a theorem. -/
@[expose] def FiveContact49Height : Prop := ∀u v:ℤ, IsCoprime u v →
    (∀j:Fin 5,forms u v j≠0) →
    pointHeight u v<2^68*((210:ℝ)^300)^2*((badProduct:ℝ)*(radical u v:ℝ))^((49:ℝ)/8)+128

 theorem absorbed_contact_height (hFive:FiveContact49Height) (u v:ℤ)
    (hc:IsCoprime u v) (hn:∀j:Fin 5,forms u v j≠0) :
    pointHeight u v<HeightSeparation318.heightConstant*(radical u v:ℝ)^((49:ℝ)/8) := by
  apply HeightSeparation318.height_constant_absorption ((210:ℝ)^300) badProduct (radical u v) _
    (by positivity) HeightSeparation318.conductor_constant_bound.le (by positivity)
    (by exact_mod_cast bad_product_bound.le) (by exact_mod_cast (radical_pos u v))
  exact hFive u v hc hn
