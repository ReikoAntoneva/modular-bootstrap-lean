import GapFamily.Analytic.Modular.Geometry.ModularCoordinate

/-!
# The actual lower fundamental-domain fiber

Below height one the open modular region has vertical fibers
`(sqrt (1-x²),1]`. Their lower endpoint stays above three quarters.
All later derivative integrals use these actual fibers.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane

def cuspLowFiber (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

def cuspLowRegion : Set ℂ := {z | z ∈ modularInterior ∧ z.im ≤ 1}

theorem continuous_cuspLowFiber : Continuous cuspLowFiber := by
  unfold cuspLowFiber
  fun_prop

theorem cuspLowFiber_lower {x : ℝ} (hx : x ∈ Icc (-1/2 : ℝ) (1/2)) :
    (3 / 4 : ℝ) ≤ cuspLowFiber x := by
  have hx2 : x ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ x + 1/2 by linarith [hx.1])]
  have he := Real.sq_sqrt (show 0 ≤ 1 - x ^ 2 by linarith)
  have hn := Real.sqrt_nonneg (1 - x ^ 2)
  change (3 / 4 : ℝ) ≤ Real.sqrt (1 - x ^ 2)
  nlinarith

theorem cuspLowFiber_le_one (x : ℝ) : cuspLowFiber x ≤ 1 := by
  exact Real.sqrt_le_iff.mpr ⟨zero_le_one, by nlinarith [sq_nonneg x]⟩

theorem cuspLowFiber_pos {x : ℝ} (hx : x ∈ Icc (-1/2 : ℝ) (1/2)) :
    0 < cuspLowFiber x := lt_of_lt_of_le (by norm_num) (cuspLowFiber_lower hx)

theorem modularInterior_iff_lowFiber (z : ℂ) :
    z ∈ modularInterior ↔ z.re ∈ Ioo (-1/2 : ℝ) (1/2) ∧ cuspLowFiber z.re < z.im := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hx : τ.re ∈ Ioo (-1/2 : ℝ) (1/2) := by
      simpa only [Set.mem_Ioo, neg_div] using abs_lt.mp hτ.2
    refine ⟨hx, (Real.sqrt_lt' τ.im_pos).mpr ?_⟩
    have hn := hτ.1
    rw [Complex.normSq_apply] at hn
    dsimp at hn ⊢
    nlinarith
  · rintro ⟨hx, hy⟩
    have hpos : 0 < z.im := (cuspLowFiber_pos ⟨hx.1.le, hx.2.le⟩).trans hy
    refine ⟨⟨z, hpos⟩, ?_, rfl⟩
    constructor
    · change 1 < Complex.normSq z
      rw [Complex.normSq_apply]
      have h := (Real.sqrt_lt' hpos).mp hy
      nlinarith
    · change |z.re| < (1 : ℝ) / 2
      exact abs_lt.mpr ⟨by simpa only [neg_div] using hx.1, hx.2⟩

theorem measurableSet_cuspLowRegion : MeasurableSet cuspLowRegion :=
  measurableSet_modularInterior.inter (measurableSet_le Complex.measurable_im measurable_const)

theorem cuspLowRegion_subset_interior : cuspLowRegion ⊆ modularInterior := fun _ hz => hz.1

theorem cuspLowRegion_eq_preimage : cuspLowRegion = Complex.measurableEquivRealProd ⁻¹'
    {p : ℝ × ℝ | p.1 ∈ Ioo (-1/2 : ℝ) (1/2) ∧ p.2 ∈ Ioc (cuspLowFiber p.1) 1} := by
  ext z
  simp only [cuspLowRegion, mem_ofPred_eq, modularInterior_iff_lowFiber, mem_preimage,
    Complex.measurableEquivRealProd_apply, mem_Ioc]
  tauto

end GapFamily.Analytic
