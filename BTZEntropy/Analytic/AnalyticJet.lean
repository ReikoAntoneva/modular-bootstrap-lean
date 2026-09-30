import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic jets with explicit remainders

Equality of jets is expressed by an actual analytic remainder divisible by
the next power of the local variable. Algebra and composition preserve this
relation, and it identifies all derivatives through the stated order.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace BTZEntropy

/-- Equality through order `N`, witnessed by a higher-order analytic remainder. -/
def analyticJetEq (N : ℕ) (f g : ℂ → ℂ) : Prop :=
  ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
    ∀ᶠ z in 𝓝 0, f z = g z + z ^ (N + 1) * R z

namespace analyticJetEq

variable {N : ℕ} {f g u v : ℂ → ℂ}

theorem refl (N : ℕ) (f : ℂ → ℂ) : analyticJetEq N f f :=
  ⟨fun _ => 0, analyticAt_const, by simp⟩

theorem of_eventuallyEq (hfg : f =ᶠ[𝓝 (0 : ℂ)] g) : analyticJetEq N f g := by
  refine ⟨fun _ => 0, analyticAt_const, ?_⟩
  filter_upwards [hfg] with z hz
  simpa using hz

theorem symm (hfg : analyticJetEq N f g) : analyticJetEq N g f := by
  obtain ⟨R, hR, he⟩ := hfg
  refine ⟨fun z => -R z, hR.neg, ?_⟩
  filter_upwards [he] with z hz
  rw [hz]
  ring

theorem trans (hfg : analyticJetEq N f g) (hgu : analyticJetEq N g u) :
    analyticJetEq N f u := by
  obtain ⟨R, hR, he⟩ := hfg
  obtain ⟨S, hS, hs⟩ := hgu
  refine ⟨fun z => R z + S z, hR.add hS, ?_⟩
  filter_upwards [he, hs] with z hz hsz
  rw [hz, hsz]
  ring

theorem add (hfg : analyticJetEq N f g) (huv : analyticJetEq N u v) :
    analyticJetEq N (fun z => f z + u z) (fun z => g z + v z) := by
  obtain ⟨R, hR, he⟩ := hfg
  obtain ⟨S, hS, hs⟩ := huv
  refine ⟨fun z => R z + S z, hR.add hS, ?_⟩
  filter_upwards [he, hs] with z hz hsz
  rw [hz, hsz]
  ring

theorem const_mul (hfg : analyticJetEq N f g) (c : ℂ) :
    analyticJetEq N (fun z => c * f z) (fun z => c * g z) := by
  obtain ⟨R, hR, he⟩ := hfg
  refine ⟨fun z => c * R z, analyticAt_const.mul hR, ?_⟩
  filter_upwards [he] with z hz
  rw [hz]
  ring

/-- The analytic hypotheses are needed only for the two cross factors. -/
theorem mul (hfg : analyticJetEq N f g) (huv : analyticJetEq N u v)
    (hg : AnalyticAt ℂ g 0) (hu : AnalyticAt ℂ u 0) :
    analyticJetEq N (fun z => f z * u z) (fun z => g z * v z) := by
  obtain ⟨R, hR, he⟩ := hfg
  obtain ⟨S, hS, hs⟩ := huv
  refine ⟨fun z => R z * u z + g z * S z, (hR.mul hu).add (hg.mul hS), ?_⟩
  filter_upwards [he, hs] with z hz hsz
  rw [hz, hsz]
  ring

/-- Equal analytic jets have equal derivatives at every retained order. -/
theorem iteratedDeriv_eq (hfg : analyticJetEq N f g)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) {n : ℕ} (hn : n ≤ N) :
    iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
  obtain ⟨R, hR, he⟩ := hfg
  have hord : ((N + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z => f z - g z) 0 := by
    apply (natCast_le_analyticOrderAt (hf.fun_sub hg)).2
    refine ⟨R, hR, ?_⟩
    filter_upwards [he] with z hz
    simpa only [sub_zero, smul_eq_mul] using (sub_eq_iff_eq_add'.2 hz)
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.fun_sub hg)).1 hord n (by omega)
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt] at hz
  exact sub_eq_zero.mp hz

end analyticJetEq

/-- An analytic function vanishing at zero has an analytic linear quotient. -/
theorem analytic_factor_zero {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ᶠ z in 𝓝 0, g z = z * G z := by
  obtain ⟨G, hG, he⟩ := hg.exists_eventuallyEq_sum_add_pow_mul 1
  refine ⟨G, hG, ?_⟩
  simpa [hg0] using he

namespace analyticJetEq

variable {N : ℕ} {f g u : ℂ → ℂ}

/-- Substitution by a zero-preserving analytic function retains the order. -/
theorem comp_zero (hfg : analyticJetEq N f g) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 = 0) :
    analyticJetEq N (fun z => f (u z)) (fun z => g (u z)) := by
  obtain ⟨R, hR, he⟩ := hfg
  obtain ⟨U, hU, huE⟩ := analytic_factor_zero hu hu0
  refine ⟨fun z => U z ^ (N + 1) * R (u z),
    (hU.pow (N + 1)).mul (hR.fun_comp_of_eq hu hu0), ?_⟩
  have ht : Tendsto u (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, hu0] using hu.continuousAt
  filter_upwards [ht.eventually he, huE] with z hz huz
  rw [hz, huz, mul_pow]
  ring

end analyticJetEq

/-- The ordinary exponential agrees with its Taylor polynomial to each finite order. -/
theorem analyticJetEq_exp_sum (N : ℕ) :
    analyticJetEq N Complex.exp
      (fun z : ℂ => ∑ j ∈ Finset.range (N + 1), z ^ j / (j.factorial : ℂ)) := by
  obtain ⟨R, hR, he⟩ := (analyticAt_cexp (z := (0 : ℂ))).exists_eventuallyEq_sum_add_pow_mul
    (N + 1)
  refine ⟨R, hR, ?_⟩
  simpa [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp] using he

/-- Exponentiating a vanishing analytic function can be truncated in its value. -/
theorem analyticJetEq_exp_comp_sum (N : ℕ) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    analyticJetEq N (fun z => Complex.exp (g z))
      (fun z => ∑ j ∈ Finset.range (N + 1), g z ^ j / (j.factorial : ℂ)) :=
  (analyticJetEq_exp_sum N).comp_zero hg hg0

namespace analyticJetEq

variable {N : ℕ} {f g : ℂ → ℂ}

/-- Exponentiation preserves equality of analytic jets. -/
theorem exp (hfg : analyticJetEq N f g) (hg : AnalyticAt ℂ g 0) :
    analyticJetEq N (fun z => Complex.exp (f z)) (fun z => Complex.exp (g z)) := by
  obtain ⟨R, hR, he⟩ := hfg
  obtain ⟨S, hS, hs⟩ := analyticJetEq_exp_sum 0
  let d : ℂ → ℂ := fun z => z ^ (N + 1) * R z
  have hd : AnalyticAt ℂ d 0 := (analyticAt_id.pow (N + 1)).mul hR
  have hd0 : d 0 = 0 := by simp [d]
  have ht : Tendsto d (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, hd0] using hd.continuousAt
  refine ⟨fun z => Complex.exp (g z) * R z * S (d z),
    (hg.cexp'.mul hR).mul (hS.fun_comp_of_eq hd hd0), ?_⟩
  filter_upwards [he, ht.eventually hs] with z hz hsz
  simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one] at hsz
  rw [hz, Complex.exp_add, hsz]
  dsimp [d]
  ring

end analyticJetEq

end BTZEntropy
