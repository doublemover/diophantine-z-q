module
public import Height13RealLog
public section
namespace KummerDetector
section Cocycle
variable {G V W : Type*} [Group G] [AddCommGroup V] [AddCommGroup W]
    [DistribMulAction G V]

/-- On an element acting trivially on the Tate module, the cocycle is a
    homomorphism on its cyclic subgroup. This pays the finite auxiliary index. -/
theorem cocycle_power (c : G → V) (hc : ∀ g k, c (g*k)=c g+g • c k)
    (hc1 : c 1=0) (h : G) (hh : ∀ x : V, h • x=x) (n : ℕ) :
    c (h^n)=n • c h := by
  induction n with
  | zero => simp [hc1]
  | succ n ih =>
    rw [pow_succ', hc, hh, ih, add_nsmul, one_nsmul]
    abel

/-- Exact source detector σ=hτ. The cocycle value of τ cancels by τ²=1;
    no independence of torsion and auxiliary fields is assumed. -/
theorem squared_conjugation_reading (c : G → V)
    (hc : ∀ g k, c (g*k)=c g+g • c k) (hc1 : c 1=0)
    (h tau : G) (hh : ∀ x : V, h • x=x) (htau : tau*tau=1)
    (b : V →+ W) (hb : ∀ x, b (tau • x)=b x) :
    b (c ((h*tau)*(h*tau)))=2 • b (c h) := by
  have ht : b (c tau)+b (c tau)=0 := by
    have h := congrArg b (hc tau tau)
    rw [htau, hc1, map_zero, map_add, hb] at h
    exact h.symm
  calc
    b (c ((h*tau)*(h*tau)))
        = b (c h)+b (c tau)+(b (c h)+b (c tau)) := by
          simp only [hc, mul_smul, hh, smul_add, map_add, hb]
    _ = (b (c h)+b (c h))+(b (c tau)+b (c tau)) := by abel
    _ = 2 • b (c h) := by rw [ht, add_zero, two_nsmul]
end Cocycle

section CentralScalar
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V]
    [Module K V] [DistribMulAction G V] [SMulCommClass G K V]

/-- The exact scalar-kernel argument: a cocycle on the Tate image becomes
    a coboundary when a nonidentity central scalar acts. Applied after
    descent from ker(rho), this contradicts rational Kummer injectivity. -/
theorem central_scalar_coboundary (c : G → V)
    (hc : ∀ g h, c (g*h)=c g+g • c h) (z : G) (scalar : K)
    (hcentral : ∀ g, z*g=g*z) (hscalar : ∀ v : V, z • v=scalar • v)
    (hnontriv : scalar-1 ≠ 0) (g : G) :
    c g = g • ((scalar-1)⁻¹ • c z)-((scalar-1)⁻¹ • c z) := by
  have h := hc z g
  rw [hcentral, hc, hscalar] at h
  have hrel : (scalar-1) • c g = g • c z-c z := by
    rw [sub_smul,one_smul]
    calc
      scalar • c g-c g = (c z+scalar • c g)-c z-c g := by abel
      _ = (c g+g • c z)-c z-c g := by rw [← h]
      _ = g • c z-c z := by abel
  calc
    c g = (scalar-1)⁻¹ • ((scalar-1) • c g) := by
      rw [← mul_smul,inv_mul_cancel₀ hnontriv,one_smul]
    _ = (scalar-1)⁻¹ • (g • c z-c z) := by rw [hrel]
    _ = _ := by rw [smul_sub,← smul_comm g ((scalar-1)⁻¹) (c z)]
end CentralScalar

section FiniteField
variable {A : Type*} [AddCommGroup A]

/-- Frobenius-squared Kummer evaluation is independent of the chosen
    division point whenever Frobenius squared fixes n-torsion. -/
theorem division_choice_independent (F : A →+ A) (n : ℕ)
    (hfix : ∀ x : A, n • x=0 → F (F x)=x)
    (r s : A) (hrs : n • r=n • s) :
    F (F r)-r=F (F s)-s := by
  have ht : n • (r-s)=0 := by rw [nsmul_sub, hrs, sub_self]
  have h := hfix (r-s) ht
  simp only [map_sub] at h
  apply sub_eq_zero.mp
  calc
    (F (F r)-r)-(F (F s)-s) = (F (F r)-F (F s))-(r-s) := by abel
    _ = 0 := by rw [h,sub_self]

/-- The exact kernel criterion uses a division point defined over the
    quadratic residue field, without inserting an extra normalization. -/
theorem evaluation_zero_iff (F : A →+ A) (r : A) :
    F (F r)-r=0 ↔ F (F r)=r := sub_eq_zero

/-- Surjectivity of F²−1 produces every n-torsion Kummer value. In the
    geometric application F²−1 is a nonzero separable isogeny. -/
theorem evaluation_surjective (F : A →+ A) (n : ℕ)
    (hsurj : Function.Surjective (fun r : A => F (F r)-r))
    (S : A) (hS : n • S=0) :
    ∃ r : A, F (F (n • r))=n • r ∧ F (F r)-r=S := by
  obtain ⟨r,hr⟩ := hsurj S
  refine ⟨r, ?_,hr⟩
  have h := congrArg (fun x : A => n • x) hr
  rw [nsmul_sub,hS] at h
  rw [map_nsmul,map_nsmul]
  exact sub_eq_zero.mp h

/-- Choosing Fr as the division point for FP proves the exact Frobenius
    equivariance consumed by the fixed +1 covector b. -/
theorem evaluation_equivariant (F : A →+ A) (r : A) :
    F (F (F r))-F r=F (F (F r)-r) := by rw [map_sub]
end FiniteField

#print axioms central_scalar_coboundary
#print axioms cocycle_power
#print axioms squared_conjugation_reading
#print axioms division_choice_independent
#print axioms evaluation_zero_iff
#print axioms evaluation_surjective
#print axioms evaluation_equivariant
end KummerDetector
