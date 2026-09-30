import BTZEntropy.Analytic.Determinant
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Smoothness of the boundary-graviton determinant

The holomorphic Euler product on the unit disc restricts to a smooth real
function. Removing its level-one factor identifies the level-two determinant
on the positive inverse-temperature axis.
-/

noncomputable section

open scoped BigOperators Topology ContDiff

namespace BTZEntropy

private def eulerBase (u : ℝ) : ℝ :=
  ∏' m : ℕ, (1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u))

private theorem eulerBase_pos {u : ℝ} (hu : 0 < u) : 0 < eulerBase u :=
  tprod_levelFactor_pos hu (by norm_num : 0 < (1 : ℕ))

private theorem eulerBase_eq_re {u : ℝ} (hu : 0 < u) :
    eulerBase u =
      (∏' m : ℕ, (1 - (Real.exp (-u) : ℂ) ^ (m + 1))).re := by
  have hp := (multipliable_levelFactor hu (by norm_num : 0 < (1 : ℕ))).map_tprod
    Complex.ofRealHom Complex.continuous_ofReal
  have he (m : ℕ) :
      ((1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ) =
        1 - (Real.exp (-u) : ℂ) ^ (m + 1) := by
    have hreal : Real.exp (-((m + 1 : ℕ) : ℝ) * u) = Real.exp (-u) ^ (m + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [Complex.ofReal_sub, Complex.ofReal_one, hreal, Complex.ofReal_pow]
  change (↑(∏' m : ℕ, (1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u))) : ℂ) =
    ∏' m : ℕ, ((1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ) at hp
  rw [show (fun m : ℕ => ((1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ)) =
    (fun m : ℕ => 1 - (Real.exp (-u) : ℂ) ^ (m + 1)) from funext he] at hp
  exact congrArg Complex.re hp

private theorem contDiffAt_eulerBase {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ eulerBase u := by
  have hball : (Real.exp (-u) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
  have heuler : ContDiffAt ℂ ∞
      (fun q : ℂ => ∏' m : ℕ, (1 - q ^ (m + 1))) (Real.exp (-u)) :=
    (ModularForm.differentiableOn_tprod_one_sub_pow.analyticAt
      (Metric.isOpen_ball.mem_nhds hball)).contDiffAt
  have hreal := heuler.real_of_complex
  have hcomp : ContDiffAt ℝ ∞
      (fun v : ℝ => (∏' m : ℕ, (1 - (Real.exp (-v) : ℂ) ^ (m + 1))).re) u :=
    hreal.comp u (f := fun v : ℝ => Real.exp (-v)) (by fun_prop)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
  exact eulerBase_eq_re hv

theorem boundaryGravitonFactor_eq_levelOneProduct {u : ℝ} (hu : 0 < u) :
    boundaryGravitonFactor u =
      ((1 - Real.exp (-u)) /
        (∏' m : ℕ, (1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u)))) ^ 2 := by
  change boundaryGravitonFactor u = ((1 - Real.exp (-u)) / eulerBase u) ^ 2
  let p : ℝ := ∏' m : ℕ, (1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u))
  have hp : 0 < p := tprod_levelFactor_pos hu (by norm_num : 0 < (2 : ℕ))
  have hpProd := multipliable_levelFactor hu (by norm_num : 0 < (2 : ℕ))
  have hpow : (∏' m : ℕ, (1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2) = p ^ 2 :=
    hpProd.tprod_pow 2
  have hdet : boundaryGravitonFactor u = (p ^ 2)⁻¹ := by
    unfold boundaryGravitonFactor
    rw [(hpProd.pow 2).tprod_inv₀ (by rw [hpow]; positivity), hpow]
  have heuler : eulerBase u = (1 - Real.exp (-u)) * p := by
    have h := tprod_eq_zero_mul'
      (f := fun m : ℕ => 1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u))
      (by simpa only [Nat.add_assoc] using hpProd)
    simpa [eulerBase, p, Nat.add_assoc] using h
  have hfactor : 1 - Real.exp (-u) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)))
  rw [hdet, heuler]
  field_simp

theorem contDiffAt_boundaryGravitonFactor {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ boundaryGravitonFactor u := by
  have hquot : ContDiffAt ℝ ∞
      (fun v : ℝ => ((1 - Real.exp (-v)) / eulerBase v) ^ 2) u :=
    ((show ContDiffAt ℝ ∞ (fun v : ℝ => 1 - Real.exp (-v)) u by fun_prop).div
      (contDiffAt_eulerBase hu) (ne_of_gt (eulerBase_pos hu))).pow 2
  apply hquot.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
  exact boundaryGravitonFactor_eq_levelOneProduct hv

theorem contDiffOn_boundaryGravitonFactor :
    ContDiffOn ℝ ∞ boundaryGravitonFactor (Set.Ioi 0) :=
  fun _ hu => (contDiffAt_boundaryGravitonFactor hu).contDiffWithinAt

theorem continuousOn_boundaryGravitonFactor :
    ContinuousOn boundaryGravitonFactor (Set.Ioi 0) :=
  contDiffOn_boundaryGravitonFactor.continuousOn

end BTZEntropy
