import GapFamily.Construction.TailErrorBudget

/-! The polynomial output-energy losses in a short-cell exterior estimate can
be paid by the fixed vacuum envelope at every energy. No upper energy bound
or choice of the later charge ratio is used. -/

noncomputable section
namespace GapFamily.Construction

private theorem self_le_exp_twice_sqrt {e : ℝ} (he : 0 ≤ e) :
    e ≤ Real.exp (2 * Real.sqrt e) := by
  have hroot : Real.sqrt e ≤ Real.exp (Real.sqrt e) := by
    linarith [Real.add_one_le_exp (Real.sqrt e)]
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg e) hroot 2
  simpa only [Real.sq_sqrt he, ← Real.exp_nat_mul, Nat.cast_ofNat] using h

/-- Fixed polynomial losses have only linear cutoff cost and square-root
output growth, including arbitrary unbounded exterior energies. -/
theorem tail_polynomial_le_exp {B e : ℝ} (hB : 0 ≤ B) (he : 1 ≤ e) (p : ℕ) :
    (1 + B + e)^p ≤ Real.exp ((p : ℝ) * (B + 2) + 2 * p * Real.sqrt e) := by
  have hbase : 1 + B + e ≤ (B + 2) * e := by nlinarith
  have hBexp : B + 2 ≤ Real.exp (B + 2) := by
    linarith [Real.add_one_le_exp (B + 2)]
  calc
    (1 + B + e)^p ≤ ((B + 2) * e)^p := pow_le_pow_left₀ (by positivity) hbase p
    _ ≤ (Real.exp (B + 2) * Real.exp (2 * Real.sqrt e))^p :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul hBexp (self_le_exp_twice_sqrt (by linarith)) (by linarith)
          (Real.exp_nonneg _)) p
    _ = Real.exp ((p : ℝ) * (B + 2) + 2 * p * Real.sqrt e) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring

/-- One lower charge threshold absorbs the entire exterior-energy growth into
the actual `exp(7 sqrt(ae))` envelope, uniformly in all larger energies. -/
theorem tail_exterior_polynomial_absorption {A B C D a e : ℝ} (p : ℕ)
    (hB : 0 ≤ B) (he : 1 ≤ e) (ha : 0 ≤ a)
    (hcharge : D + 2 * p ≤ 7 * Real.sqrt a) :
    A * (1 + B + e)^p * Real.exp (C * B + D * Real.sqrt e) ≤
      Real.exp (|A| + (C + p) * B + 2 * p) * Real.exp (7 * Real.sqrt (a * e)) := by
  have hA : A ≤ Real.exp |A| := by
    linarith [le_abs_self A, Real.add_one_le_exp |A|]
  have h1 : A * (1 + B + e)^p ≤
      Real.exp |A| * Real.exp ((p : ℝ) * (B + 2) + 2 * p * Real.sqrt e) :=
    mul_le_mul hA (tail_polynomial_le_exp hB he p) (by positivity) (Real.exp_nonneg _)
  calc
    _ ≤ (Real.exp |A| * Real.exp ((p : ℝ) * (B + 2) + 2 * p * Real.sqrt e)) *
        Real.exp (C * B + D * Real.sqrt e) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = Real.exp (|A| + (C + p) * B + 2 * p +
        (D + 2 * p) * Real.sqrt e) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      rw [← Real.exp_add, Real.sqrt_mul ha]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hcharge (Real.sqrt_nonneg e)
      nlinarith

/-- The sufficient charge threshold depends only on the fixed square-root
growth and polynomial degree, and hence can be selected before the ratio. -/
theorem exists_tail_exterior_charge_threshold (D : ℝ) (p : ℕ) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a ≥ a₀, D + 2 * p ≤ 7 * Real.sqrt a := by
  refine ⟨(max 1 ((D + 2 * p) / 7))^2, ?_, ?_⟩
  · have h : 1 ≤ max 1 ((D + 2 * p) / 7) := le_max_left _ _
    nlinarith
  · intro a ha
    have hx : 0 ≤ max 1 ((D + 2 * p) / 7) := le_trans (by norm_num) (le_max_left _ _)
    have hroot := Real.sqrt_le_sqrt ha
    rw [Real.sqrt_sq hx] at hroot
    have hmax := le_max_right (1 : ℝ) ((D + 2 * p) / 7)
    linarith

end GapFamily.Construction
