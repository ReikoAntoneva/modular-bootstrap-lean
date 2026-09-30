import GapFamily.Analytic.Cusp.Green.CuspGreenSourceRepresentative
import Mathlib.Topology.Order.ProjIcc

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory
open scoped Topology

/-- A continuous measured-collar value embeds as its literal height-truncated lift.
The matching real-coordinate function needs no regularity outside this collar. -/
theorem cuspGreenSourceEmbedding_toLp_ae (L : ℝ) (hL : 0 ≤ L)
    (c : C(CuspGreenCollar 0 L, ℂ)) (v : ℝ → ℂ)
    (hc : ∀ t : CuspGreenCollar 0 L, c t = v t) :
    cuspGreenSourceEmbedding L
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ c) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im ∧ τ.im ≤ Real.exp L then
        Real.sqrt τ.im • v (Real.log τ.im) else 0) := by
  let ψ : ℝ → ℂ := fun t => c (Set.projIcc 0 L hL t)
  have hψ : Continuous ψ := c.continuous.comp continuous_projIcc
  have hsource : cuspGreenCollarSource 0 L ψ hψ =
      ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ c := by
    unfold cuspGreenCollarSource
    congr 1
    ext t
    change c (Set.projIcc 0 L hL t) = c t
    rw [Set.projIcc_val]
  have hrep := cuspGreenSourceEmbedding_continuous_ae L hL ψ hψ
  rw [hsource] at hrep
  filter_upwards [hrep] with τ hτ
  rw [hτ]
  by_cases hτL : 1 < τ.im ∧ τ.im ≤ Real.exp L
  · simp only [ite_eq_left hτL, cuspLift]
    have hlog : Real.log τ.im ∈ Icc 0 L :=
      ⟨(Real.log_pos hτL.1).le, (Real.log_le_iff_le_exp τ.im_pos).mpr hτL.2⟩
    change Real.sqrt τ.im • c (Set.projIcc 0 L hL (Real.log τ.im)) = _
    rw [Set.projIcc_of_mem hL hlog]
    exact congrArg (fun z : ℂ => Real.sqrt τ.im • z) (hc ⟨Real.log τ.im, hlog⟩)
  · simp only [ite_eq_right hτL]

end GapFamily.Analytic
