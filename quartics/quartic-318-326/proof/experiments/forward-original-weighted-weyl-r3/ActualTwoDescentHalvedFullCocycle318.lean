module
public import ActualTwoDescentFullConnectingExactness318
public section
noncomputable section
namespace ActualTwoDescentHalvedFullCocycle318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisLocallyConstant318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open groupCohomology

open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticHOneKernel318 ActualTwoDescentTorsionIntoFullCocycles318

/-- A full elliptic cocycle whose double is a coboundary becomes E[2]-valued by subtracting an ACTUAL half-point coboundary. -/
lemma actual_halved_full_values (n : F) (hn : n ≠ 0) (z : continuousFullCocycles n hn)
    (Q R : Point (algebraMap F Qbar n)) (hR : R+R=Q)
    (hQ : ∀ σ : Gal, z.val σ+z.val σ=halfDifference n hn Q σ) :
    ∀ σ : Gal, (z.val σ-halfDifference n hn R σ)+(z.val σ-halfDifference n hn R σ)=0 := by
  intro σ
  have h := congrArg (fun P => halfDifference n hn P σ) hR
  simp only [halfDifference,map_add] at h
  have hq := hQ σ
  dsimp [halfDifference] at hq ⊢
  calc
    _=(z.val σ+z.val σ)-((galoisPointHom σ n hn R+galoisPointHom σ n hn R)-(R+R)) := by abel
    _=0 := by rw [h,hq]; abel

def halvedFullCocycle (n : F) (hn : n ≠ 0) (z : continuousFullCocycles n hn)
    (R : Point (algebraMap F Qbar n))
    (ht : ∀ σ : Gal, (z.val σ-halfDifference n hn R σ)+(z.val σ-halfDifference n hn R σ)=0) :
    continuousCocycles n := by
  let w : continuousFullCocycles n hn := z-fullBoundary n hn R
  let χ : Gal →* Multiplicative (closedTwoTorsion n) :=
    { toFun := fun σ => Multiplicative.ofAdd ⟨w.val σ,by
        simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using ht σ⟩
      map_one' := by apply Subtype.ext; exact cocycles₁_map_one w.val
      map_mul' := by
        intro σ τ
        apply Subtype.ext
        change w.val (σ*τ)=w.val σ+w.val τ
        have h := (mem_cocycles₁_iff _).mp w.val.property σ τ
        change w.val (σ*τ)=galoisPointHom σ n hn (w.val τ)+w.val σ at h
        rw [actual_two_torsion_fixed σ n hn (w.val τ) (ht τ)] at h
        exact h.trans (add_comm _ _) }
  refine ⟨χ,?_⟩
  apply IsLocallyConstant.desc χ (fun T : Multiplicative (closedTwoTorsion n) => (T.toAdd : Point (algebraMap F Qbar n)))
  · exact w.property
  · intro a b h; exact Subtype.ext h

lemma actual_halved_full_cocycle_value (n : F) (hn : n ≠ 0) (z : continuousFullCocycles n hn)
    (R : Point (algebraMap F Qbar n)) (ht) :
    torsionFullCocycle n hn (halvedFullCocycle n hn z R ht)=z-fullBoundary n hn R := by
  apply Subtype.ext; apply Subtype.ext; funext σ; rfl

end ActualTwoDescentHalvedFullCocycle318
