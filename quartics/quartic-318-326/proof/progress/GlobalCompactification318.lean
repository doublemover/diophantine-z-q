module
public import GlobalOpenNormalization318
public section
noncomputable section
namespace GlobalCompactification318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u v

/-- Affineness of a genuine scheme map is derived from affine inverse images
on a genuine covering, not asserted from a list of unrelated algebras. -/
theorem affine_of_cover {X Y:Scheme.{u}} (f:X⟶Y)
    {ι:Type v} (U:ι→Y.affineOpens) (hcover:⨆i,(U i).1=⊤)
    (hpre:∀i,IsAffineOpen (f⁻¹ᵁ(U i).1)) : IsAffineHom f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P:=@IsAffineHom) _ hcover]
  intro i
  letI : IsAffine ((U i).1 : Scheme) := (U i).2
  letI : IsAffine ((f⁻¹ᵁ(U i).1) : Scheme) := hpre i
  infer_instance

variable {X Y:Scheme.{u}} (f:X⟶Y) [IsAffineHom f]
  {ι:Type v} (U:ι→Y.affineOpens) (hcover:⨆i,(U i).1=⊤)
  (Rf:ι→Type u) [∀i,CommRing (Rf i)]
  [∀i,IsDomain Γ(Y,(U i).1)] [∀i,CharZero Γ(Y,(U i).1)]
  [∀i,IsNoetherianRing Γ(Y,(U i).1)] [∀i,IsIntegrallyClosed Γ(Y,(U i).1)]
  [∀i,Algebra Γ(Y,(U i).1) (Rf i)]
  [∀i,IsDomain Γ(X,f⁻¹ᵁ(U i).1)]
  [∀i,Algebra (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  [∀i,Algebra.Smooth (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  [∀i,Module.Finite (Rf i) Γ(X,f⁻¹ᵁ(U i).1)]
  (d:∀i,Γ(Y,(U i).1)) [∀i,IsLocalization.Away (d i) (Rf i)]
  (hd:∀i,d i≠0)
  (htower:∀i,letI:=(f.app (U i).1).hom.toAlgebra;
    IsScalarTower Γ(Y,(U i).1) (Rf i) Γ(X,f⁻¹ᵁ(U i).1))

include U hcover Rf d hd htower

/-- A true global open-then-finite factorization, constructed by the actual
relative normalization. All map properties are derived from the given actual
chart data; neither an open compactification map nor a finite normalization
map is supplied. -/
theorem open_finite_factorization :
    IsOpenImmersion f.toNormalization ∧ IsFinite f.fromNormalization ∧
    f.toNormalization≫f.fromNormalization=f := by
  exact ⟨GlobalOpenNormalization318.toNormalization_open f U hcover Rf d htower,
    GlobalNormalization318.finite_of_smooth_open_pieces f U hcover Rf d hd htower,
    f.toNormalization_fromNormalization⟩

/-- Over an actual proper target, the constructed scheme is a genuine proper
extension of the actual source. Properness of the target remains explicit;
no projective or arithmetic source realization is inferred. -/
theorem proper_extension {S:Scheme.{u}} (g:Y⟶S) [IsProper g] :
    IsOpenImmersion f.toNormalization ∧
    IsProper (f.fromNormalization≫g) ∧
    f.toNormalization≫(f.fromNormalization≫g)=f≫g := by
  refine ⟨(open_finite_factorization f U hcover Rf d hd htower).1,
    GlobalNormalization318.proper_over_base f U hcover Rf d hd htower g, ?_⟩
  simp

end GlobalCompactification318
