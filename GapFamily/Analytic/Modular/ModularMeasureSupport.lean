import GapFamily.Analytic.Modular.ModularVolume
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory
open scoped ENNReal NNReal

/-- Every nonempty open set has positive actual hyperbolic volume. -/
theorem upperHalfPlane_volume_pos_of_isOpen (O : Set UpperHalfPlane)
    (hO : IsOpen O) (hne : O.Nonempty) :
    0 < (volume : Measure UpperHalfPlane) O := by
  have hopen : IsOpen (UpperHalfPlane.coe '' O) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hO
  have hpositive : 0 < (volume : Measure ℂ) (UpperHalfPlane.coe '' O) :=
    hopen.measure_pos (volume : Measure ℂ) (hne.image _)
  have hsupport : UpperHalfPlane.coe '' O ⊆
      Function.support (fun z : ℂ => (↑((1 / ‖z.im‖₊) ^ 2 : NNReal) : ENNReal)) := by
    rintro z ⟨τ, _, rfl⟩
    have hp := τ.im_pos
    simp only [Function.mem_support]
    simpa using hp.ne'
  rw [UpperHalfPlane.volume_eq_lintegral, setLIntegral_pos_iff (by fun_prop),
    inter_eq_right.mpr hsupport]
  exact hpositive

/-- The genuine invariant volume has full support on the upper half-plane. -/
theorem upperHalfPlane_volume_support :
    (volume : Measure UpperHalfPlane).support = univ := by
  let : (volume : Measure UpperHalfPlane).IsOpenPosMeasure :=
    ⟨fun O hO hne => (upperHalfPlane_volume_pos_of_isOpen O hO hne).ne'⟩
  exact Measure.support_eq_univ

/-- The support of the actual modular measure is exactly the closed
fundamental domain, including its boundary. -/
theorem modularMeasure_support : modularMeasure.support = ModularGroup.fd := by
  change ((volume : Measure UpperHalfPlane).restrict ModularGroup.fd).support = ModularGroup.fd
  apply Subset.antisymm
  · intro τ hτ
    have h := (Measure.support_restrict_subset
      (μ := (volume : Measure UpperHalfPlane)) (s := ModularGroup.fd)) hτ
    simpa only [ModularGroup.isClosed_fd.closure_eq] using h.1
  · have hinterior := Measure.interior_inter_support
      (μ := (volume : Measure UpperHalfPlane)) (s := ModularGroup.fd)
    rw [upperHalfPlane_volume_support, inter_univ, ← ModularGroup.fdo_eq_interior_fd]
      at hinterior
    have hclosure := closure_minimal hinterior
      (Measure.isClosed_support :
        IsClosed ((volume : Measure UpperHalfPlane).restrict ModularGroup.fd).support)
    simpa only [← ModularGroup.fd_eq_closure_fdo] using hclosure

end GapFamily.Analytic
