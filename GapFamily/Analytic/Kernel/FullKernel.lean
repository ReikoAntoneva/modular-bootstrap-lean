import GapFamily.Analytic.Kernel.KernelAnalytic
import GapFamily.Analytic.Foundation.PhysicalBound
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralJointBound

/-!
# The full canonical energy kernel

The central coefficient is the actual threshold quotient of the continued
Poincaré seed. The entire kernel adds that coefficient to the normally
convergent higher kernel. Its restriction to real energies is kept complex
valued here; reality and the Fourier–Laplace identification are separate
statements. The corrected kernel adds the scalar rank-one term, not an atom.
-/

noncomputable section

namespace GapFamily.Analytic

open Real

/-- The central term occurs only when both spins are nonzero. -/
def centralKernel (j J : ℤ) : ℂ :=
  if j = 0 ∨ J = 0 then 0 else 2 * PoincareCentralZeta.centralZeta j J 0

/-- The full entire-energy formula `Q_hol`. -/
def fullKernelHol (j J : ℤ) (e E : ℂ) : ℂ :=
  centralKernel j J + higherKernel j J e E

/-- The scalar rank-one correction, as an ordinary density numerator. -/
def scalarRankKernel (j J : ℤ) (e E : ℝ) : ℝ :=
  if j = 0 ∧ J = 0 then 12 * sqrt e * sqrt E else 0

/-- The actual central-plus-higher-plus-rank-one energy kernel on real energies. -/
def correctedKernel (j J : ℤ) (e E : ℝ) : ℂ :=
  fullKernelHol j J e E + (scalarRankKernel j J e E : ℂ)

@[simp] theorem centralKernel_scalar_output (J : ℤ) : centralKernel 0 J = 0 := by
  simp [centralKernel]

@[simp] theorem centralKernel_scalar_input (j : ℤ) : centralKernel j 0 = 0 := by
  simp [centralKernel]

@[simp] theorem fullKernelHol_scalar_output_zero (J : ℤ) (E : ℂ) :
    fullKernelHol 0 J 0 E = 0 := by
  simp [fullKernelHol]

@[simp] theorem fullKernelHol_scalar_input_zero (j : ℤ) (e : ℂ) :
    fullKernelHol j 0 e 0 = 0 := by
  simp [fullKernelHol]

theorem differentiable_fullKernelHol (j J : ℤ) :
    Differentiable ℂ (fun p : ℂ × ℂ => fullKernelHol j J p.1 p.2) :=
  (differentiable_const _).add (differentiable_higherKernel j J)

theorem continuous_fullKernelHol (j J : ℤ) :
    Continuous (fun p : ℂ × ℂ => fullKernelHol j J p.1 p.2) :=
  (differentiable_fullKernelHol j J).continuous

theorem differentiable_fullKernelHol_comp (j J : ℤ) (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun z => fullKernelHol j J (f z) (g z)) :=
  (differentiable_const _).add (differentiable_higherKernel_comp j J f g hf hg)

theorem continuous_scalarRankKernel (j J : ℤ) :
    Continuous (fun p : ℝ × ℝ => scalarRankKernel j J p.1 p.2) := by
  unfold scalarRankKernel
  split_ifs
  · fun_prop
  · exact continuous_const

theorem continuous_correctedKernel (j J : ℤ) :
    Continuous (fun p : ℝ × ℝ => correctedKernel j J p.1 p.2) := by
  exact ((continuous_fullKernelHol j J).comp
    ((Complex.continuous_ofReal.comp continuous_fst).prodMk
      (Complex.continuous_ofReal.comp continuous_snd))).add
        (Complex.continuous_ofReal.comp (continuous_scalarRankKernel j J))

theorem norm_scalarRankKernel_le (j J : ℤ) (e E : ℝ) :
    ‖(scalarRankKernel j J e E : ℂ)‖ ≤ 12 * sqrt e * sqrt E := by
  by_cases h : j = 0 ∧ J = 0
  · simp only [scalarRankKernel, if_pos h, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 12 * sqrt e * sqrt E by positivity)]
    exact le_rfl
  · simp only [scalarRankKernel, if_neg h, Complex.ofReal_zero, norm_zero]
    positivity

/-- One arithmetic constant controls the central term for all integer spins,
including the scalar row and column where that term is absent. -/
theorem exists_centralKernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ j J : ℤ,
      ‖centralKernel j J‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)|) := by
  obtain ⟨C, hC, hbound⟩ :=
    PoincareCentralZeta.exists_centralZeta_zero_joint_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro j J
  by_cases h : j = 0 ∨ J = 0
  · simp only [centralKernel, if_pos h, norm_zero]
    positivity
  · rw [centralKernel, if_neg h, norm_mul, Complex.norm_ofNat]
    have hb := hbound j J (fun hj => h (Or.inl hj)) (fun hJ => h (Or.inr hJ))
    rw [abs_mul] at hb
    nlinarith

/-- A physical bound for the full corrected kernel, with one constant uniform in both spins
and both physical energies. -/
theorem exists_correctedKernel_physical_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (j J : ℤ) (e E : ℝ),
      |(j : ℝ)| ≤ e → |(J : ℝ)| ≤ E →
      ‖correctedKernel j J e E‖ ≤
        C * (|(j : ℝ)| * |(J : ℝ)| + sqrt e * sqrt E) := by
  obtain ⟨C, hC, hbound⟩ := exists_centralKernel_bound
  refine ⟨C + 64 * π ^ 2 + 12, by positivity, ?_⟩
  intro j J e E he hE
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hh := norm_higherKernel_physical_le_sqrt j J e E he hE
  rw [sqrt_mul he0] at hh
  calc
    ‖correctedKernel j J e E‖ ≤
        ‖centralKernel j J‖ + ‖higherKernel j J e E‖ +
          ‖(scalarRankKernel j J e E : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * (|(j : ℝ)| * |(J : ℝ)|) +
        64 * π ^ 2 * (sqrt e * sqrt E) + 12 * sqrt e * sqrt E :=
      add_le_add (add_le_add (hbound j J) hh) (norm_scalarRankKernel_le j J e E)
    _ ≤ _ := by
      nlinarith [mul_nonneg (show 0 ≤ 64 * π ^ 2 + 12 by positivity)
        (mul_nonneg (abs_nonneg (j : ℝ)) (abs_nonneg (J : ℝ))),
        mul_nonneg hC.le (mul_nonneg (sqrt_nonneg e) (sqrt_nonneg E))]

/-- Strong scalar endpoint vanishing of `Q_hol`, before the square-root rank term. -/
theorem norm_fullKernelHol_scalar_output_le (J : ℤ) (e E : ℝ)
    (he : 0 ≤ e) (hE : |(J : ℝ)| ≤ E) :
    ‖fullKernelHol 0 J e E‖ ≤ 32 * π ^ 2 * (e * E) := by
  simpa only [fullKernelHol, centralKernel_scalar_output, zero_add] using
    norm_higherKernel_physical_le_mul 0 J e E (by simpa using he) hE

theorem norm_fullKernelHol_scalar_input_le (j : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : 0 ≤ E) :
    ‖fullKernelHol j 0 e E‖ ≤ 32 * π ^ 2 * (e * E) := by
  simpa only [fullKernelHol, centralKernel_scalar_input, zero_add] using
    norm_higherKernel_physical_le_mul j 0 e E he (by simpa using hE)

end GapFamily.Analytic
