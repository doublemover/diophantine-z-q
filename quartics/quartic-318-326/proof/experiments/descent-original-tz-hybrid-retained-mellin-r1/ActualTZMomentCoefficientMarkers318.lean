module
public import Mathlib
public section
namespace ActualTZMomentCoefficientMarkers318

/-- Independent formal coarse and paired-digit variables. For a
quadratic expression this mixed finite difference reads the
coefficient of the joint monomial, not just its values mod p. -/
@[expose] def mixedProbe (f : ℤ→ℤ→ℤ) : ℤ := f 1 1-f 1 0-f 0 1+f 0 0

def oddProbe (f : ℤ→ℤ) : ℤ := f 1-f 0

@[expose] def quadraticProbe (f : ℤ→ℤ) : ℤ := f 1-2*f 0+f (-1)

theorem nonlinear_same_node (Q a c t D E : ℤ) :
    mixedProbe (fun m k =>
      (Q*(m+t+k)^2+a*(m+t+k)+c-D*k) -
      (Q*(m+t+E)^2+a*(m+t+E)+c))=2*Q := by
  unfold mixedProbe
  ring

theorem nonlinear_distinct_copies (Q Q' a a' t t' c c' x' : ℤ) :
    quadraticProbe (fun m =>
      (Q*(m+t)^2+a*(m+t)+c) - (Q'*(x'+t')^2+a'*(x'+t')+c'))=2*Q := by
  unfold quadraticProbe
  ring

/-- Same fine×digit monomial in a distinct face corner. The
deleted alpha direction is not a candidate witness. -/
theorem linear_face_marker (aα aβ C D E F : ℤ) :
    mixedProbe (fun h k =>
      (aα-aβ)*h*k+C*h+D*k+E - F*h)=aα-aβ := by
  unfold mixedProbe
  ring

theorem marked_vertex_marker (a C D E : ℤ) :
    mixedProbe (fun h k => -a*h*k+C*h+D*k+E) = -a := by
  unfold mixedProbe
  ring

/-- Multiplying by W and adding distinct residues and wrap constants
does not affect which degree-two direction supplied the witness. -/
theorem physical_mixedProbe (f g : ℤ→ℤ→ℤ) (W b b' s : ℤ) :
    mixedProbe (fun h k => W*(f h k-g h k)+b-b'-s)=W*(mixedProbe f-mixedProbe g) := by
  unfold mixedProbe
  ring

end ActualTZMomentCoefficientMarkers318
