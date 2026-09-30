import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace GapFamily.Analytic.HeightAwareComposition
open Finset

/-- The exact finite Faà di Bruno coefficient, with one factorial per inner derivative. -/
def heightCompositionConstant (n : ℕ) (A : ℕ → ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, A c.length * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)

private theorem sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Fin c.length, c.partSize i = n := by
  simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))

/-- In every Faà di Bruno partition the source-height powers cancel exactly. -/
theorem partition_height_cancel {n : ℕ} (c : OrderedFinpartition n)
    (A : ℕ → ℝ) (H Y σ : ℝ) (hH : 0 < H) :
    (A c.length * H ^ (σ - (c.length : ℝ))) *
        (∏ i : Fin c.length, ((c.partSize i).factorial : ℝ) * H / Y ^ c.partSize i) =
      (A c.length * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) * H ^ σ / Y ^ n := by
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum, sum_partSize,
    Real.rpow_sub_natCast hH.ne']
  field_simp [hH.ne']

/-- The exact partition constant is nonnegative whenever the supplied derivative constants are. -/
theorem heightCompositionConstant_nonneg (n : ℕ) (A : ℕ → ℝ)
    (hA : ∀ k, k ≤ n → 0 ≤ A k) : 0 ≤ heightCompositionConstant n A := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (hA c.length c.length_le) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

/-- The ordinary composition estimate preserves H^σ and Y^(-n), rather than losing
one source-height factor per derivative. All hypotheses concern the actual derivatives. -/
theorem norm_iteratedFDeriv_comp_height {f g : ℂ → ℂ} {z : ℂ} (n : ℕ)
    (hf : ContDiffAt ℝ n f (g z)) (hg : ContDiffAt ℝ n g z)
    (A : ℕ → ℝ) (H Y σ : ℝ) (hH : 0 < H) (_hY : 0 < Y)
    (hA : ∀ k, k ≤ n → 0 ≤ A k)
    (houter : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k f (g z)‖ ≤ A k * H ^ (σ - (k : ℝ)))
    (hinner : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j g z‖ ≤ (j.factorial : ℝ) * H / Y ^ j) :
    ‖iteratedFDeriv ℝ n (f ∘ g) z‖ ≤ heightCompositionConstant n A * H ^ σ / Y ^ n := by
  rw [iteratedFDeriv_comp hf hg le_rfl, FormalMultilinearSeries.taylorComp]
  calc
    _ ≤ ∑ c : OrderedFinpartition n,
        ‖(ftaylorSeries ℝ f (g z)).compAlongOrderedFinpartition (ftaylorSeries ℝ g z) c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition n,
        (A c.length * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) * H ^ σ / Y ^ n := by
      apply Finset.sum_le_sum
      intro c _
      calc
        _ ≤ ‖iteratedFDeriv ℝ c.length f (g z)‖ *
            ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) g z‖ :=
          c.norm_compAlongOrderedFinpartition_le _ _
        _ ≤ (A c.length * H ^ (σ - (c.length : ℝ))) *
            (∏ i : Fin c.length, ((c.partSize i).factorial : ℝ) * H / Y ^ c.partSize i) := by
          apply mul_le_mul (houter c.length c.length_le)
            (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
              hinner (c.partSize i) (c.partSize_pos i) (c.partSize_le i)))
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          exact mul_nonneg (hA c.length c.length_le) (Real.rpow_nonneg hH.le _)
        _ = _ := partition_height_cancel c A H Y σ hH
    _ = _ := by
      simp only [heightCompositionConstant, div_eq_mul_inv, Finset.sum_mul]

end GapFamily.Analytic.HeightAwareComposition
