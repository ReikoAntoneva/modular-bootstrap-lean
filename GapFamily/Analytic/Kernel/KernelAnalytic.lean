import GapFamily.Analytic.Arithmetic.Kloosterman
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Local normal convergence of the actual higher kernel

The intact product-minus-one kernel has a summable denominator-square majorant
uniform on bounded sets of both complex energy variables. This proves joint
local uniform convergence, and holomorphic dependence on either energy.
The continued zero-order Kloosterman-zeta term is outside this module.
-/

noncomputable section

namespace GapFamily.Analytic

open Filter Set Metric
open scoped Topology

/-- A summable scalar majorant for intact higher-kernel summands. -/
def higherKernelMajorant (B : ℝ) (n : ℕ) : ℝ :=
  (B * Real.exp B) / ((n + 1 : ℕ) : ℝ) ^ 2

theorem summable_higherKernelMajorant (B : ℝ) :
    Summable (higherKernelMajorant B) := by
  change Summable (fun n : ℕ => (B * Real.exp B) / ((n + 1 : ℕ) : ℝ) ^ 2)
  simpa [div_eq_mul_inv] using
    ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num))).mul_left
        (B * Real.exp B)

/-- An argument bound controls every denominator without any cancellation assumption. -/
theorem norm_higherKernelTerm_le_majorant (j J : ℤ) (e E : ℂ) (B : ℝ)
    (hB : ‖higherKernelArgPlus j J e E‖ + ‖higherKernelArgMinus j J e E‖ ≤ B)
    (n : ℕ) : ‖higherKernelTerm j J e E n‖ ≤ higherKernelMajorant B n := by
  have hd : 1 ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hn : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  have hb := norm_cosRoot_mul_sub_one_div_le
    (higherKernelArgPlus j J e E) (higherKernelArgMinus j J e E)
    (((n + 1 : ℕ) : ℝ) ^ 2) hd
  simp only [Complex.ofReal_pow, Complex.ofReal_natCast] at hb
  unfold higherKernelTerm
  rw [norm_mul]
  calc
    _ ≤ ‖cosRoot (higherKernelArgPlus j J e E / ((n + 1 : ℕ) : ℂ) ^ 2) *
        cosRoot (higherKernelArgMinus j J e E / ((n + 1 : ℕ) : ℂ) ^ 2) - 1‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (norm_kloostermanSum_div_le_one j J n)
    _ ≤ _ := hb
    _ ≤ higherKernelMajorant B n := by
      unfold higherKernelMajorant
      have hB0 : 0 ≤ B := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hB
      gcongr

/-- Both energy arguments are continuous jointly. -/
theorem continuous_higherKernelArgPlus (j J : ℤ) :
    Continuous (fun p : ℂ × ℂ => higherKernelArgPlus j J p.1 p.2) := by
  unfold higherKernelArgPlus
  fun_prop

theorem continuous_higherKernelArgMinus (j J : ℤ) :
    Continuous (fun p : ℂ × ℂ => higherKernelArgMinus j J p.1 p.2) := by
  unfold higherKernelArgMinus
  fun_prop

/-- A compact set has one summable majorant for all its energy pairs. -/
theorem exists_higherKernelMajorant_on_compact (j J : ℤ) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n p, p ∈ K →
      ‖higherKernelTerm j J p.1 p.2 n‖ ≤ higherKernelMajorant B n := by
  have hc : Continuous (fun p : ℂ × ℂ =>
      ‖higherKernelArgPlus j J p.1 p.2‖ + ‖higherKernelArgMinus j J p.1 p.2‖) :=
    (continuous_higherKernelArgPlus j J).norm.add (continuous_higherKernelArgMinus j J).norm
  obtain ⟨B, hB, hbound⟩ := (hK.image hc).isBounded.exists_pos_norm_le
  refine ⟨B, hB.le, fun n p hp => norm_higherKernelTerm_le_majorant j J p.1 p.2 B ?_ n⟩
  exact (le_abs_self _).trans (hbound _ (mem_image_of_mem _ hp))

/-- Local normal convergence: absolute values have a summable uniform majorant on every compact. -/
theorem higherKernelTerm_normal_on_compact (j J : ℤ) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n p, p ∈ K →
      ‖higherKernelTerm j J p.1 p.2 n‖ ≤ u n := by
  obtain ⟨B, _, hB⟩ := exists_higherKernelMajorant_on_compact j J hK
  exact ⟨higherKernelMajorant B, summable_higherKernelMajorant B, hB⟩

/-- The same normal-convergence bound applies to every bounded parameter set. -/
theorem higherKernelTerm_normal_on_bounded (j J : ℤ) {K : Set (ℂ × ℂ)}
    (hK : Bornology.IsBounded K) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n p, p ∈ K →
      ‖higherKernelTerm j J p.1 p.2 n‖ ≤ u n := by
  obtain ⟨u, hu, hbound⟩ := higherKernelTerm_normal_on_compact j J hK.isCompact_closure
  exact ⟨u, hu, fun n p hp => hbound n p (subset_closure hp)⟩

/-- Absolute-value partial sums also converge uniformly on compact energy sets. -/
theorem norm_higherKernelTerm_tendstoUniformlyOn_compact (j J : ℤ)
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N (p : ℂ × ℂ) => ∑ n ∈ Finset.range N, ‖higherKernelTerm j J p.1 p.2 n‖)
      (fun p => ∑' n, ‖higherKernelTerm j J p.1 p.2 n‖) atTop K := by
  obtain ⟨u, hu, hbound⟩ := higherKernelTerm_normal_on_compact j J hK
  apply tendstoUniformlyOn_tsum_nat hu
  intro n p hp
  simpa only [norm_norm] using hbound n p hp

/-- The actual finite partial sums converge jointly uniformly on each compact parameter set. -/
theorem higherKernel_tendstoUniformlyOn_compact (j J : ℤ) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N (p : ℂ × ℂ) => ∑ n ∈ Finset.range N, 2 * higherKernelTerm j J p.1 p.2 n)
      (fun p => higherKernel j J p.1 p.2) atTop K := by
  obtain ⟨u, hu, hbound⟩ := higherKernelTerm_normal_on_compact j J hK
  have h := tendstoUniformlyOn_tsum_nat (hu.mul_left 2) (f := fun n (p : ℂ × ℂ) =>
    2 * higherKernelTerm j J p.1 p.2 n) (s := K) (by
      intro n p hp
      rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      exact mul_le_mul_of_nonneg_left (hbound n p hp) (by norm_num))
  simpa only [higherKernel, tsum_mul_left] using h

/-- The complete higher-kernel series converges locally uniformly in both complex energies. -/
theorem higherKernel_tendstoLocallyUniformly (j J : ℤ) :
    TendstoLocallyUniformly
      (fun N (p : ℂ × ℂ) => ∑ n ∈ Finset.range N, 2 * higherKernelTerm j J p.1 p.2 n)
      (fun p => higherKernel j J p.1 p.2) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  exact fun K hK => higherKernel_tendstoUniformlyOn_compact j J hK

/-- Every summand is jointly continuous. -/
theorem continuous_higherKernelTerm (j J : ℤ) (n : ℕ) :
    Continuous (fun p : ℂ × ℂ => higherKernelTerm j J p.1 p.2 n) := by
  unfold higherKernelTerm
  exact continuous_const.mul
    (((cosRoot_continuous.comp ((continuous_higherKernelArgPlus j J).div_const _)).mul
      (cosRoot_continuous.comp ((continuous_higherKernelArgMinus j J).div_const _))).sub
      continuous_const)

/-- The actual summed higher kernel is jointly continuous. -/
theorem continuous_higherKernel (j J : ℤ) :
    Continuous (fun p : ℂ × ℂ => higherKernel j J p.1 p.2) := by
  apply (higherKernel_tendstoLocallyUniformly j J).continuous
  exact Filter.Frequently.of_forall fun N =>
    continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_higherKernelTerm j J n)

private theorem differentiable_tsum_of_closedBall_majorant {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ι → E → F} (hf : ∀ n, Differentiable ℂ (f n))
    (hbound : ∀ x : E, ∃ u : ι → ℝ, Summable u ∧
      ∀ n y, y ∈ closedBall x 2 → ‖f n y‖ ≤ u n) :
    Differentiable ℂ (fun x => ∑' n, f n x) := by
  intro x
  obtain ⟨u, hu, hb⟩ := hbound x
  have hderiv : ∀ n y, y ∈ ball x 1 → ‖fderiv ℂ (f n) y‖ ≤ 2 * u n := by
    intro n y hy
    have hy2 : y ∈ closedBall x 2 := by
      exact mem_closedBall.mpr (le_trans (mem_ball.mp hy).le (by norm_num))
    have hmaps : MapsTo (f n) (ball y 1) (closedBall (f n y) (2 * u n)) := by
      intro z hz
      have hz2 : z ∈ closedBall x 2 := by
        apply mem_closedBall.mpr
        calc
          dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
          _ ≤ 2 := by linarith [mem_ball.mp hy, mem_ball.mp hz]
      rw [mem_closedBall, dist_eq_norm]
      calc
        ‖f n z - f n y‖ ≤ ‖f n z‖ + ‖f n y‖ := norm_sub_le _ _
        _ ≤ u n + u n := add_le_add (hb n z hz2) (hb n y hy2)
        _ = 2 * u n := by ring
    simpa using Complex.norm_fderiv_le_div_of_mapsTo_ball
      (hf n).differentiableOn hmaps (show (0 : ℝ) < 1 by norm_num)
  have hs : Summable (fun n => f n x) :=
    Summable.of_norm_bounded hu (fun n => hb n x (by simp))
  exact (hasFDerivAt_tsum_of_isPreconnected (hu.mul_left 2) isOpen_ball
    (convex_ball x 1).isPreconnected
    (fun n y _ => (hf n y).hasFDerivAt) hderiv
    (show x ∈ ball x 1 by simp) hs (show x ∈ ball x 1 by simp)).differentiableAt

/-- Every intact summand is jointly complex differentiable in both energies. -/
theorem differentiable_higherKernelTerm_joint (j J : ℤ) (n : ℕ) :
    Differentiable ℂ (fun p : ℂ × ℂ => higherKernelTerm j J p.1 p.2 n) := by
  have hc : Differentiable ℂ cosRoot := fun z => (cosRoot_analyticAt z).differentiableAt
  have hp : Differentiable ℂ (fun p : ℂ × ℂ => higherKernelArgPlus j J p.1 p.2) := by
    unfold higherKernelArgPlus
    fun_prop
  have hm : Differentiable ℂ (fun p : ℂ × ℂ => higherKernelArgMinus j J p.1 p.2) := by
    unfold higherKernelArgMinus
    fun_prop
  unfold higherKernelTerm
  simp only [div_eq_mul_inv]
  exact (differentiable_const _).mul (((hc.comp (hp.mul_const _)).mul
    (hc.comp (hm.mul_const _))).sub (differentiable_const _))

/-- The actual higher kernel is jointly complex differentiable. -/
theorem differentiable_higherKernel (j J : ℤ) :
    Differentiable ℂ (fun p : ℂ × ℂ => higherKernel j J p.1 p.2) := by
  have hs : Differentiable ℂ
      (fun p : ℂ × ℂ => ∑' n, higherKernelTerm j J p.1 p.2 n) := by
    apply differentiable_tsum_of_closedBall_majorant
      (fun n => differentiable_higherKernelTerm_joint j J n)
    intro p
    exact higherKernelTerm_normal_on_compact j J (isCompact_closedBall p 2)
  exact (differentiable_const _).mul hs

/-- Composition of one summand with two entire energy curves is entire. -/
theorem differentiable_higherKernelTerm_comp (j J : ℤ) (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (n : ℕ) :
    Differentiable ℂ (fun z => higherKernelTerm j J (f z) (g z) n) := by
  have hpair : Differentiable ℂ (fun z => (f z, g z)) := hf.prodMk hg
  simpa only [Function.comp_def] using (differentiable_higherKernelTerm_joint j J n).comp hpair

/-- The higher kernel is holomorphic along every pair of entire energy curves. -/
theorem differentiable_higherKernel_comp (j J : ℤ) (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun z => higherKernel j J (f z) (g z)) := by
  have hpair : Differentiable ℂ (fun z => (f z, g z)) := hf.prodMk hg
  simpa only [Function.comp_def] using (differentiable_higherKernel j J).comp hpair

/-- Entire dependence on the input energy, with arbitrary fixed complex output energy. -/
theorem higherKernel_analyticAt_input (j J : ℤ) (e E : ℂ) :
    AnalyticAt ℂ (higherKernel j J e) E :=
  (differentiable_higherKernel_comp j J (fun _ => e) id
    (differentiable_const e) differentiable_id).analyticAt E

/-- Entire dependence on the output energy, with arbitrary fixed complex input energy. -/
theorem higherKernel_analyticAt_output (j J : ℤ) (e E : ℂ) :
    AnalyticAt ℂ (fun z => higherKernel j J z E) e :=
  (differentiable_higherKernel_comp j J id (fun _ => E)
    differentiable_id (differentiable_const E)).analyticAt e

/-- Energy differentiation commutes with the locally uniform partial-sum limit. -/
theorem higherKernel_comp_tendstoLocallyUniformly_deriv (j J : ℤ) (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    TendstoLocallyUniformly
      (fun N => deriv (fun z => ∑ n ∈ Finset.range N,
        2 * higherKernelTerm j J (f z) (g z) n))
      (deriv (fun z => higherKernel j J (f z) (g z))) atTop := by
  have hlim := (higherKernel_tendstoLocallyUniformly j J).comp
    (fun z => (f z, g z)) (hf.continuous.prodMk hg.continuous)
  rw [← tendstoLocallyUniformlyOn_univ] at hlim ⊢
  exact hlim.deriv (Filter.Eventually.of_forall fun N =>
    (Differentiable.fun_sum fun n _ =>
      (differentiable_higherKernelTerm_comp j J f g hf hg n).const_mul 2).differentiableOn)
    isOpen_univ

end GapFamily.Analytic
