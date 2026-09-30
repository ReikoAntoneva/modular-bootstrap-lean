import GapFamily.Analytic.Transform.LaplaceDifferenceMajorant
import GapFamily.Analytic.Transform.LaplaceConeMajorant

/-!
# The regularized cone Laplace weight

The scalar and nonzero frequency estimates give one ordinary majorant for
the physical same-parameter cone weight throughout every closed strip
strictly inside `Re s > 0`. This interface carries the linear energy growth
needed when integrating an actual continued Poincaré seed.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- The cone factor after the input height difference. -/
def coneLaplaceDifferenceWeight (s : ℂ) (J t d E : ℝ) : ℂ :=
  ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) * (thermalHeightDifference t d E : ℂ)

private theorem cone_base_pos {J E : ℝ} (hE : |J| < E) :
    0 < E ^ 2 - J ^ 2 := by
  have hsub : 0 < E - |J| := sub_pos.mpr hE
  have hsum : 0 < E + |J| := by linarith [abs_nonneg J]
  nlinarith [mul_pos hsub hsum, sq_abs J]

/-- The zero frequency cone convention agrees with the scalar weight. -/
theorem coneLaplaceDifferenceWeight_zero (s : ℂ) (t d : ℝ) {E : ℝ} (hE : 0 < E) :
    coneLaplaceDifferenceWeight s 0 t d E = scalarLaplaceDifferenceWeight s t d E := by
  rw [scalarLaplaceDifferenceWeight_eq_sq s t d hE]
  simp only [coneLaplaceDifferenceWeight, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero]

/-- Energy continuity holds throughout the open physical cone. -/
theorem continuousOn_coneLaplaceDifferenceWeight (s : ℂ) (J t d : ℝ) :
    ContinuousOn (coneLaplaceDifferenceWeight s J t d) (Ioi |J|) := by
  have hp : ContinuousOn (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1))
      (Ioi |J|) :=
    (by fun_prop : Continuous (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ))).continuousOn.cpow_const
      (fun E hE => Or.inl (cone_base_pos hE))
  exact hp.mul (by unfold thermalHeightDifference; fun_prop)

/-- At each physical energy the cone weight is entire in the same complex
parameter used by the spatial kernel and the continued seed. -/
theorem differentiable_coneLaplaceDifferenceWeight (J t d : ℝ) {E : ℝ}
    (hE : |J| < E) :
    Differentiable ℂ (fun s : ℂ => coneLaplaceDifferenceWeight s J t d E) := by
  unfold coneLaplaceDifferenceWeight
  apply Differentiable.mul_const
  apply Differentiable.const_cpow
  · fun_prop
  · exact Or.inl (Complex.ofReal_ne_zero.mpr (cone_base_pos hE).ne')

/-- A fixed frequency, including zero, admits one ordinary majorant for the
whole real-part strip, with the linear energy factor already included. -/
theorem coneLaplaceDifferenceWeight_majorant {a b t d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hd : 0 ≤ d) (J : ℝ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi |J|) ∧
      ∀ (s : ℂ), a ≤ s.re → s.re ≤ b → ∀ E ∈ Ioi |J|,
        ‖coneLaplaceDifferenceWeight s J t d E‖ * (1 + E) ≤ g E := by
  by_cases hJ : J = 0
  · subst J
    refine ⟨scalarLaplaceDifferenceMajorant a b t d, ?_, ?_⟩
    · simpa only [abs_zero] using integrableOn_scalarLaplaceDifferenceMajorant ha hab ht d
    · intro s hsa hsb E hE
      have hE0 : 0 < E := by simpa only [abs_zero, mem_Ioi] using hE
      rw [coneLaplaceDifferenceWeight_zero s t d hE0]
      exact norm_scalarLaplaceDifferenceWeight_mul_linear_le hsa hsb hd hE0
  · obtain ⟨g, hg, hbound⟩ := laplaceCone_difference_majorant hJ ha ht hd b
    refine ⟨g, hg, ?_⟩
    intro s hsa hsb E hE
    have hE0 : 0 < E := (abs_nonneg J).trans_lt hE
    have hw : 0 ≤ 1 + E := by linarith
    simpa only [coneLaplaceDifferenceWeight, thermalHeightDifference, Complex.ofReal_mul,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hw, mul_assoc]
      using hbound s hsa hsb E hE

/-- Ordinary absolute integrability of the weight with its linear energy
factor, on every fixed physical frequency slice. -/
theorem integrableOn_coneLaplaceDifferenceWeight_mul_linear {s : ℂ} (hs : 0 < s.re)
    {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) (J : ℝ) :
    IntegrableOn (fun E : ℝ => coneLaplaceDifferenceWeight s J t d E * (1 + E : ℝ))
      (Ioi |J|) := by
  obtain ⟨g, hg, hbound⟩ := coneLaplaceDifferenceWeight_majorant hs le_rfl ht hd J
  apply hg.mono'
  · exact ((continuousOn_coneLaplaceDifferenceWeight s J t d).mul
      (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    have hE0 : 0 < E := (abs_nonneg J).trans_lt hE
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + E)]
    exact hbound s le_rfl le_rfl E hE

end GapFamily.Analytic
