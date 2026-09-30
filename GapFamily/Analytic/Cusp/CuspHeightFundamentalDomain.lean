import GapFamily.Analytic.Poincare.PoincareAnalytic
import GapFamily.Analytic.Cusp.CuspHeightInequality

noncomputable section
namespace GapFamily.Analytic
open Complex Matrix Matrix.SpecialLinearGroup Set
open scoped MatrixGroups UpperHalfPlane

/-- The nonidentity cusp classes have a genuinely nonzero lower-left entry. -/
theorem cuspBottomRow_first_ne_zero_of_ne_identity (q : CuspCoset)
    (hq : q ≠ identityCuspCoset) : cuspBottomRow q 0 ≠ 0 := by
  intro hc
  have hrel : QuotientGroup.rightRel cuspInfinity (1 : SL(2, ℤ)) q.out := by
    rw [QuotientGroup.rightRel_apply, inv_one, mul_one]
    exact hc
  have he := Quotient.sound hrel
  change identityCuspCoset = Quotient.mk _ q.out at he
  rw [q.out_eq] at he
  exact hq he.symm

/-- The closed fundamental domain has a positive universal lower height. -/
theorem half_le_im_of_mem_fd {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    (1 / 2 : ℝ) ≤ τ.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
  nlinarith [τ.im_pos]

/-- The pinned integer Pi norm is the maximum of the two real absolute values. -/
theorem cuspBottomRow_norm_eq_max (q : CuspCoset) :
    ‖cuspBottomRow q‖ =
      max |(cuspBottomRow q 0 : ℝ)| |(cuspBottomRow q 1 : ℝ)| := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]

/-- A uniform row-decay height bound on the whole unbounded closed fundamental domain. -/
theorem nonidentity_cusp_height_le (q : CuspCoset) (hq : q ≠ identityCuspCoset)
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    (q.out • τ).im ≤ 2 / ‖cuspBottomRow q‖ := by
  have hc : (1 : ℝ) ≤ |(cuspBottomRow q 0 : ℝ)| := by
    exact_mod_cast Int.one_le_abs (cuspBottomRow_first_ne_zero_of_ne_identity q hq)
  have hb := cusp_row_height_denominator_bound (cuspBottomRow q 0 : ℝ)
    (cuspBottomRow q 1 : ℝ) τ.re τ.im hc hτ.2 (half_le_im_of_mem_fd hτ)
  have hn : Complex.normSq ((cuspBottomRow q 0 : ℂ) * τ + cuspBottomRow q 1) =
      (((cuspBottomRow q 0 : ℝ) * τ.re + (cuspBottomRow q 1 : ℝ)) ^ 2 +
        (cuspBottomRow q 0 : ℝ) ^ 2 * τ.im ^ 2) := by
    simp [Complex.normSq_apply, pow_two]
    ring
  rw [← cuspBottomRow_norm_eq_max, ← hn] at hb
  have hr : 0 < ‖cuspBottomRow q‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_int_pair _ (cuspBottomRow_ne_zero q))
  have hd : 0 < Complex.normSq ((cuspBottomRow q 0 : ℂ) * τ + cuspBottomRow q 1) := by
    nlinarith [mul_pos hr τ.im_pos]
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  change τ.im / Complex.normSq ((cuspBottomRow q 0 : ℂ) * τ + cuspBottomRow q 1) ≤ _
  exact (div_le_div_iff₀ hd hr).mpr (by simpa only [mul_comm] using hb)

/-- The exact height majorant also bounds positive powers uniformly over the closed domain. -/
theorem nonidentity_cusp_height_rpow_le (q : CuspCoset) (hq : q ≠ identityCuspCoset)
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) {σ : ℝ} (hσ : 0 ≤ σ) :
    (q.out • τ).im ^ σ ≤ (2 : ℝ) ^ σ * ‖cuspBottomRow q‖ ^ (-σ) := by
  calc
    _ ≤ (2 / ‖cuspBottomRow q‖) ^ σ :=
      Real.rpow_le_rpow (q.out • τ).im_pos.le (nonidentity_cusp_height_le q hq hτ) hσ
    _ = _ := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _),
        Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]

/-- Integer-row summability gives one finite majorant for all nonidentity cusp heights. -/
theorem summable_nonidentity_cusp_height_majorant {σ : ℝ} (hσ : 2 < σ) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      (2 : ℝ) ^ σ * ‖cuspBottomRow q‖ ^ (-σ)) := by
  exact (((EisensteinSeries.summable_one_div_norm_rpow hσ).comp_injective
    cuspBottomRow_injective).subtype _).mul_left _

/-- The actual zero-energy seed has the same uniform summable row majorant. -/
theorem norm_nonidentity_complexPoincareTerm_le (J : ℤ) (s : ℂ)
    (hs : 0 ≤ s.re) (q : CuspCoset) (hq : q ≠ identityCuspCoset)
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    ‖complexPoincareTerm 0 J s τ q‖ ≤
      (2 : ℝ) ^ s.re * ‖cuspBottomRow q‖ ^ (-s.re) := by
  rw [complexPoincareTerm_out, norm_complexPointSeed]
  simp only [Complex.zero_re, mul_zero, zero_mul, Real.exp_zero, mul_one]
  exact nonidentity_cusp_height_rpow_le q hq hτ hs

/-- Every nonidentity cusp image has height at most the reciprocal input height. -/
theorem nonidentity_cusp_height_mul_im_le_one (q : CuspCoset)
    (hq : q ≠ identityCuspCoset) (τ : UpperHalfPlane) :
    (q.out • τ).im * τ.im ≤ 1 := by
  have hc : (1 : ℝ) ≤ |(cuspBottomRow q 0 : ℝ)| := by
    exact_mod_cast Int.one_le_abs (cuspBottomRow_first_ne_zero_of_ne_identity q hq)
  have hc2 : (1 : ℝ) ≤ (cuspBottomRow q 0 : ℝ) ^ 2 := by
    nlinarith [sq_abs (cuspBottomRow q 0 : ℝ)]
  have hn : Complex.normSq ((cuspBottomRow q 0 : ℂ) * τ + cuspBottomRow q 1) =
      (((cuspBottomRow q 0 : ℝ) * τ.re + (cuspBottomRow q 1 : ℝ)) ^ 2 +
        (cuspBottomRow q 0 : ℝ) ^ 2 * τ.im ^ 2) := by
    simp [Complex.normSq_apply, pow_two]
    ring
  have hd : τ.im ^ 2 ≤
      Complex.normSq ((cuspBottomRow q 0 : ℂ) * τ + cuspBottomRow q 1) := by
    rw [hn]
    nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg τ.im),
      sq_nonneg ((cuspBottomRow q 0 : ℝ) * τ.re + (cuspBottomRow q 1 : ℝ))]
  have hdpos := (sq_pos_of_pos τ.im_pos).trans_le hd
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  change (τ.im / Complex.normSq ((cuspBottomRow q 0 : ℂ) * τ + cuspBottomRow q 1)) * τ.im ≤ 1
  rw [div_mul_eq_mul_div]
  exact (div_le_one hdpos).mpr (by simpa only [pow_two] using hd)

/-- Splitting off a nonnegative input-height weight preserves explicit row decay. -/
theorem weighted_nonidentity_cusp_height_rpow_le
    (q : CuspCoset) (hq : q ≠ identityCuspCoset) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) {α σ : ℝ} (hα : 0 ≤ α) (hασ : α ≤ σ) :
    τ.im ^ α * (q.out • τ).im ^ σ ≤
      (2 : ℝ) ^ (σ - α) * ‖cuspBottomRow q‖ ^ (-(σ - α)) := by
  have hp : (τ.im * (q.out • τ).im) ^ α ≤ 1 := by
    have hh : τ.im * (q.out • τ).im ≤ 1 := by
      simpa only [mul_comm] using nonidentity_cusp_height_mul_im_le_one q hq τ
    simpa only [Real.one_rpow] using Real.rpow_le_rpow
      (mul_nonneg τ.im_pos.le (q.out • τ).im_pos.le) hh hα
  calc
    _ = (τ.im * (q.out • τ).im) ^ α * (q.out • τ).im ^ (σ - α) := by
      rw [Real.mul_rpow τ.im_pos.le (q.out • τ).im_pos.le, mul_assoc,
        ← Real.rpow_add (q.out • τ).im_pos]
      congr 2
      ring
    _ ≤ (q.out • τ).im ^ (σ - α) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
        (Real.rpow_nonneg (q.out • τ).im_pos.le (σ - α))
    _ ≤ _ := nonidentity_cusp_height_rpow_le q hq hτ (sub_nonneg.mpr hασ)

/-- Literal zero-energy cusp terms obey the weighted bound, uniformly in spin. -/
theorem norm_weighted_nonidentity_complexPoincareTerm_le (J : ℤ) (s : ℂ)
    (q : CuspCoset) (hq : q ≠ identityCuspCoset) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) {α : ℝ} (hα : 0 ≤ α) (hαs : α ≤ s.re) :
    τ.im ^ α * ‖complexPoincareTerm 0 J s τ q‖ ≤
      (2 : ℝ) ^ (s.re - α) * ‖cuspBottomRow q‖ ^ (-(s.re - α)) := by
  rw [complexPoincareTerm_out, norm_complexPointSeed]
  simp only [Complex.zero_re, mul_zero, zero_mul, Real.exp_zero, mul_one]
  exact weighted_nonidentity_cusp_height_rpow_le q hq hτ hα hαs

/-- One explicit summable row majorant controls the weighted family on a full exponent strip. -/
theorem weighted_nonidentityPoincare_normal_on_strip {α a b : ℝ}
    (hα : 0 ≤ α) (ha : 2 < a - α) (hb : 2 < b - α) :
    ∃ u : {q : CuspCoset // q ≠ identityCuspCoset} → ℝ,
      Summable u ∧ ∀ (J : ℤ) (q : {q : CuspCoset // q ≠ identityCuspCoset})
        (s : ℂ) (τ : UpperHalfPlane), a ≤ s.re → s.re ≤ b → τ ∈ ModularGroup.fd →
        τ.im ^ α * ‖complexPoincareTerm 0 J s τ q‖ ≤ u q := by
  refine ⟨fun q => (2 : ℝ) ^ (a - α) * ‖cuspBottomRow q‖ ^ (-(a - α)) +
      (2 : ℝ) ^ (b - α) * ‖cuspBottomRow q‖ ^ (-(b - α)),
    (summable_nonidentity_cusp_height_majorant ha).add
      (summable_nonidentity_cusp_height_majorant hb), ?_⟩
  intro J q s τ has hsb hτ
  rw [complexPoincareTerm_out, norm_complexPointSeed]
  simp only [Complex.zero_re, mul_zero, zero_mul, Real.exp_zero, mul_one]
  calc
    _ ≤ τ.im ^ α * ((q.val.out • τ).im ^ a + (q.val.out • τ).im ^ b) :=
      mul_le_mul_of_nonneg_left (rpow_le_add_endpoint (q.val.out • τ).im_pos has hsb)
        (Real.rpow_nonneg τ.im_pos.le α)
    _ = τ.im ^ α * (q.val.out • τ).im ^ a + τ.im ^ α * (q.val.out • τ).im ^ b := mul_add _ _ _
    _ ≤ _ := add_le_add
      (weighted_nonidentity_cusp_height_rpow_le q q.property hτ hα (by linarith))
      (weighted_nonidentity_cusp_height_rpow_le q q.property hτ hα (by linarith))

/-- The concrete quarter input weight is normally controlled near the shifted exponent 5/2. -/
theorem shifted_nonidentityPoincare_quarter_weight_majorant :
    ∃ u : {q : CuspCoset // q ≠ identityCuspCoset} → ℝ,
      Summable u ∧ ∀ (J : ℤ) (q : {q : CuspCoset // q ≠ identityCuspCoset})
        (κ : ℂ) (τ : UpperHalfPlane), ‖κ‖ ≤ (1 / 8 : ℝ) → τ ∈ ModularGroup.fd →
        τ.im ^ (1 / 4 : ℝ) * ‖complexPoincareTerm 0 J ((5 / 2 : ℂ) + κ) τ q‖ ≤ u q := by
  obtain ⟨u, hu, hbound⟩ := weighted_nonidentityPoincare_normal_on_strip
    (α := (1 / 4 : ℝ)) (a := (19 / 8 : ℝ)) (b := (21 / 8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨u, hu, ?_⟩
  intro J q κ τ hκ hτ
  have hre := (abs_le.mp ((Complex.abs_re_le_norm κ).trans hκ))
  apply hbound J q _ τ ?_ ?_ hτ <;> norm_num [Complex.add_re] <;> linarith [hre.1, hre.2]

end GapFamily.Analytic
