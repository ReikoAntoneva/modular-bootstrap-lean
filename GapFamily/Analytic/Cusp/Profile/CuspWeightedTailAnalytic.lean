import GapFamily.Analytic.Cusp.Profile.CuspWeightedTailLp
import GapFamily.Analytic.Cusp.Profile.CuspWeightedTailBCFProfile
import GapFamily.Analytic.Foundation.PositiveBCFPower
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

/-- A globally defined Hilbert family from the literal bounded profile. It agrees
with the weighted actual term throughout its proved positive-exponent region. -/
def cuspWeightedTailAnalyticTerm (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) (s : ℂ) : ModularHilbert :=
  BoundedContinuousFunction.toLp 2 modularMeasure ℂ
    (cuspTailAmplitudeBCF J α hα q *
      PositiveBCFPower.positivePower (cuspTailClippedHeight q)
        (continuous_cuspTailClippedHeight q) (cuspTailClippedHeight_pos q)
        2 (cuspTailClippedHeight_le_two q) (s - (α : ℂ)))

/-- Each actual weighted coset term is holomorphic in Hilbert norm once Re s>α. -/
theorem cuspWeightedTailAnalyticTerm_analyticAt (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) {s : ℂ} (hs : α < s.re) :
    AnalyticAt ℂ (cuspWeightedTailAnalyticTerm J α hα q) s := by
  have hp : AnalyticAt ℂ (fun z : ℂ =>
      PositiveBCFPower.positivePower (cuspTailClippedHeight q)
        (continuous_cuspTailClippedHeight q) (cuspTailClippedHeight_pos q)
        2 (cuspTailClippedHeight_le_two q) (z - (α : ℂ))) s := by
    exact (PositiveBCFPower.positivePower_analyticAt _ _ _ _ _
      (by simpa using sub_pos.mpr hs)).comp (by fun_prop)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := UpperHalfPlane →ᵇ ℂ)
    (F := ModularHilbert) (BoundedContinuousFunction.toLp 2 modularMeasure ℂ) _).comp_of_eq
      (analyticAt_const.mul hp) rfl

/-- The clipped construction is the literal weighted summand for the actual measure. -/
theorem cuspWeightedTailAnalyticTerm_ae (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) {s : ℂ} (hs : α < s.re) :
    cuspWeightedTailAnalyticTerm J α hα q s =ᵐ[modularMeasure] cuspWeightedTailTerm J s α q := by
  have hfd : ∀ᵐ τ ∂modularMeasure, τ ∈ ModularGroup.fd := ae_restrict_mem measurableSet_fd
  have hp := BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ
    (cuspTailAmplitudeBCF J α hα q *
      PositiveBCFPower.positivePower (cuspTailClippedHeight q)
        (continuous_cuspTailClippedHeight q) (cuspTailClippedHeight_pos q)
        2 (cuspTailClippedHeight_le_two q) (s - (α : ℂ)))
  filter_upwards [hp, hfd] with τ hp hτ
  change cuspWeightedTailAnalyticTerm J α hα q s τ = _ at hp
  rw [hp]
  change cuspTailAmplitudeBCF J α hα q τ *
    PositiveBCFPower.positivePower _ _ _ _ _ (s - (α : ℂ)) τ = _
  rw [PositiveBCFPower.positivePower_apply _ _ _ _ _
    (by simpa using sub_pos.mpr hs)]
  exact (weighted_complexPoincareTerm_eq_cuspTailAmplitudeBCF J α hα s q hτ).symm

/-- The analytic term is the previously proved actual L² class. -/
theorem cuspWeightedTailAnalyticTerm_eq_lp (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) {s : ℂ} (hs : α < s.re) :
    cuspWeightedTailAnalyticTerm J α hα q s = cuspWeightedTailLp J s hα hs.le q :=
  Lp.ext ((cuspWeightedTailAnalyticTerm_ae J α hα q hs).trans
    (cuspWeightedTailLp_ae J s hα hs.le q).symm)

/-- The actual nonidentity weighted tail, as one total parameter family. -/
def cuspWeightedTailAnalytic (J : ℤ) (α : ℝ) (hα : 0 ≤ α) (s : ℂ) : ModularHilbert :=
  ∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, cuspWeightedTailAnalyticTerm J α hα q s

/-- Absolute norm convergence precedes every use of the summed analytic family. -/
theorem summable_norm_cuspWeightedTailAnalyticTerm (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {s : ℂ} (hgap : 2 < s.re - α) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ‖cuspWeightedTailAnalyticTerm J α hα q s‖) := by
  have hs : α < s.re := by linarith
  simp_rw [cuspWeightedTailAnalyticTerm_eq_lp J α hα _ hs]
  exact summable_norm_cuspWeightedTailLp J s hα hgap

/-- Its value is the genuinely convergent previously constructed Hilbert tail. -/
theorem cuspWeightedTailAnalytic_eq_tail (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {s : ℂ} (hgap : 2 < s.re - α) :
    cuspWeightedTailAnalytic J α hα s = cuspWeightedTail J s hα hgap := by
  apply tsum_congr
  intro q
  exact cuspWeightedTailAnalyticTerm_eq_lp J α hα q (by linarith)

/-- The summed family has the actual ordinary weighted nonidentity-series representative. -/
theorem cuspWeightedTailAnalytic_ae (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {s : ℂ} (hgap : 2 < s.re - α) :
    cuspWeightedTailAnalytic J α hα s =ᵐ[modularMeasure]
      (fun τ => ∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
        cuspWeightedTailTerm J s α q τ) := by
  rw [cuspWeightedTailAnalytic_eq_tail J α hα hgap]
  exact cuspWeightedTail_ae J s hα hgap

/-- The full actual weighted nonidentity tail is holomorphic in Hilbert norm
on Re s>α+2, by its explicit summable row majorant. -/
theorem cuspWeightedTailAnalytic_analyticAt (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {s : ℂ} (hgap : 2 < s.re - α) :
    AnalyticAt ℂ (cuspWeightedTailAnalytic J α hα) s := by
  let δ : ℝ := (s.re - α - 2) / 2
  let a : ℝ := s.re - δ
  let b : ℝ := s.re + δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have ha : 2 < a - α := by dsimp [a, δ]; linarith
  have hb : 2 < b - α := by dsimp [b, δ]; linarith
  have hstrip (w : ℂ) (hw : w ∈ Metric.ball s δ) : a ≤ w.re ∧ w.re ≤ b := by
    have hd : ‖w - s‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hr := abs_lt.mp ((Complex.abs_re_le_norm (w - s)).trans_lt hd)
    simp only [Complex.sub_re] at hr
    dsimp [a, b]
    constructor <;> linarith [hr.1, hr.2]
  obtain ⟨u, hu, hbound⟩ := weighted_nonidentityPoincare_normal_on_strip hα ha hb
  let C : ℝ := (measureUnivNNReal modularMeasure : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  have hmajor : Summable (fun q => C * |u q|) := hu.abs.mul_left C
  have hnorm : ∀ (q : {q : CuspCoset // q ≠ identityCuspCoset}) (w : ℂ),
      w ∈ Metric.ball s δ → ‖cuspWeightedTailAnalyticTerm J α hα q w‖ ≤ C * |u q| := by
    intro q w hw
    obtain ⟨hwa, hwb⟩ := hstrip w hw
    have haw : α < w.re := by linarith
    apply Lp.norm_le_of_ae_bound (abs_nonneg (u q))
    have hfd : ∀ᵐ τ ∂modularMeasure, τ ∈ ModularGroup.fd := ae_restrict_mem measurableSet_fd
    filter_upwards [cuspWeightedTailAnalyticTerm_ae J α hα q haw, hfd] with τ hrep hτ
    rw [hrep, cuspWeightedTailTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg τ.im_pos.le α)]
    exact (hbound J q w τ hwa hwb hτ).trans (le_abs_self _)
  have hdiff : DifferentiableOn ℂ (cuspWeightedTailAnalytic J α hα) (Metric.ball s δ) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hmajor ?_ Metric.isOpen_ball hnorm
    intro q w hw
    have haw : α < w.re := by have := (hstrip w hw).1; linarith
    exact (cuspWeightedTailAnalyticTerm_analyticAt J α hα q haw).differentiableAt.differentiableWithinAt
  exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))

theorem cuspWeightedTailAnalytic_analyticOnNhd (J : ℤ) (α : ℝ) (hα : 0 ≤ α) :
    AnalyticOnNhd ℂ (cuspWeightedTailAnalytic J α hα) {s : ℂ | 2 < s.re - α} :=
  fun _ hs => cuspWeightedTailAnalytic_analyticAt J α hα hs

/-- The unweighted actual nonidentity zero-energy family is H-holomorphic on Re s>2. -/
theorem cuspWeightedTailAnalytic_zero_weight_analyticAt (J : ℤ) {s : ℂ} (hs : 2 < s.re) :
    AnalyticAt ℂ (cuspWeightedTailAnalytic J 0 (by norm_num)) s :=
  cuspWeightedTailAnalytic_analyticAt J 0 (by norm_num) (by simpa using hs)

/-- In particular the actual quarter-weight shifted source is H-holomorphic near κ=0. -/
theorem shifted_cuspWeightedTailAnalytic_quarter_analyticAt_zero (J : ℤ) :
    AnalyticAt ℂ (fun κ : ℂ => cuspWeightedTailAnalytic J (1 / 4) (by norm_num)
      ((5 / 2 : ℂ) + κ)) 0 :=
  (cuspWeightedTailAnalytic_analyticAt J (1 / 4) (by norm_num)
    (s := (5 / 2 : ℂ)) (by norm_num)).comp_of_eq (by fun_prop) (by simp)

end GapFamily.Analytic
