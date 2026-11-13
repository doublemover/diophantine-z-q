module
public import PELOriginalDirichletPolygon318
public section
noncomputable section
namespace PELActualPolygonHomeomorph318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318 PELOriginalKleinHomeomorph318
open PELOriginalDirichletPolygon318 PELQuaternionRealRepresentation318
set_option maxHeartbeats 1800000

theorem scaled_radius (A B : ℝ) : (A/(alpha*beta))^2+(B/beta)^2=A^2/1050+B^2/5 := by
  field_simp [alpha_pos.ne',beta_pos.ne']
  ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

@[expose] def polygonDisk (p : planePolygon) : Disk :=
  ⟨(p.val.1/(alpha*beta),p.val.2/beta),by
    rw [scaled_radius]
    exact lt_of_le_of_lt (radius_bound _ _ p.property) (by norm_num)⟩

theorem inverse_scaled (p : planePolygon) :
    scaledFirst (fromDisk (polygonDisk p))=p.val.1 ∧
    scaledSecond (fromDisk (polygonDisk p))=p.val.2 := by
  have h := to_from (polygonDisk p)
  have hA := congrArg (fun x : Disk => x.val.1) h
  have hB := congrArg (fun x : Disk => x.val.2) h
  change firstDisk (fromDisk (polygonDisk p))=p.val.1/(alpha*beta) at hA
  change secondDisk (fromDisk (polygonDisk p))=p.val.2/beta at hB
  constructor
  · unfold scaledFirst
    rw [hA]
    field_simp [alpha_pos.ne',beta_pos.ne'] <;> ring
  · unfold scaledSecond
    rw [hB]
    field_simp [beta_pos.ne'] <;> ring

@[expose] def polygonInverse (p : planePolygon) : originalDomain :=
  ⟨fromDisk (polygonDisk p),by
    change inequalities (scaledFirst _) (scaledSecond _)
    rw [(inverse_scaled p).1,(inverse_scaled p).2]
    exact p.property⟩

theorem coordinate_inverse (p : planePolygon) : polygonCoordinate (polygonInverse p)=p := by
  apply Subtype.ext
  exact Prod.ext (inverse_scaled p).1 (inverse_scaled p).2

theorem continuous_polygonCoordinate : Continuous polygonCoordinate := by
  apply Continuous.subtype_mk
  exact scaled_continuous.comp continuous_subtype_val

theorem continuous_polygonInverse : Continuous polygonInverse := by
  apply Continuous.subtype_mk
  apply continuous_fromDisk.comp
  apply Continuous.subtype_mk
  exact ((continuous_fst.comp continuous_subtype_val).div_const (alpha*beta)).prodMk
    ((continuous_snd.comp continuous_subtype_val).div_const beta)

/-- The exact rational finite halfplane polygon is homeomorphic to the
actual compact original upper-half-plane overdomain, not an abstract drawing. -/
@[expose] def originalPolygonHomeomorph : originalDomain ≃ₜ planePolygon where
  toFun := polygonCoordinate
  invFun := polygonInverse
  left_inv x := polygonCoordinate_injective (coordinate_inverse (polygonCoordinate x))
  right_inv := coordinate_inverse
  continuous_toFun := continuous_polygonCoordinate
  continuous_invFun := continuous_polygonInverse

instance originalDomainCompact : CompactSpace originalDomain :=
  isCompact_iff_compactSpace.mp originalDomain_compact

instance actualPolygonCompact : CompactSpace planePolygon := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr originalPolygonHomeomorph.surjective,← Set.image_univ]
  exact isCompact_univ.image originalPolygonHomeomorph.continuous
end PELActualPolygonHomeomorph318
