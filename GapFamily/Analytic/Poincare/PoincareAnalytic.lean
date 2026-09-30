import GapFamily.Analytic.Poincare.Poincare
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Complex parameters of the convergent energy correction

The zero-energy subtraction of the actual cusp-quotient Poincaré sum has
normal convergence for complex input energy and `re s > 0`. This module
does not define or assume a continuation of the zero-energy spin seed.
-/

namespace GapFamily.Analytic

open Complex Filter Set Metric Matrix Matrix.SpecialLinearGroup
open scoped Real Topology MatrixGroups UpperHalfPlane

noncomputable section


/-- The point seed with both energy and convergence exponent complexified. -/
def complexPointSeed (E : ℂ) (J : ℤ) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℂ) ^ s * Complex.exp
    (-2 * (Real.pi : ℂ) * E * z.im +
      ((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I)

theorem complexPointSeed_translation (E : ℂ) (J : ℤ) (s : ℂ)
    (n : ℤ) (z : UpperHalfPlane) :
    complexPointSeed E J s (ModularGroup.T ^ n • z) = complexPointSeed E J s z := by
  unfold complexPointSeed
  rw [ModularGroup.im_T_zpow_smul, ModularGroup.re_T_zpow_smul]
  congr 1
  have harg :
      -2 * (Real.pi : ℂ) * E * z.im +
          ((2 * Real.pi * (J : ℝ) * (z.re + n) : ℝ) : ℂ) * I =
        (-2 * (Real.pi : ℂ) * E * z.im +
          ((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I) +
          ((J * n : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem complexPointSeed_cusp (E : ℂ) (J : ℤ) (s : ℂ)
    (g : SL(2, ℤ)) (hg : g ∈ cuspInfinity) (z : UpperHalfPlane) :
    complexPointSeed E J s (g • z) = complexPointSeed E J s z := by
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hg
  rw [hn, complexPointSeed_translation]

theorem complexPointSeed_coset_eq (E : ℂ) (J : ℤ) (s : ℂ) (z : UpperHalfPlane)
    {g h : SL(2, ℤ)} (hgh : QuotientGroup.rightRel cuspInfinity g h) :
    complexPointSeed E J s (g • z) = complexPointSeed E J s (h • z) := by
  have hmem : h * g⁻¹ ∈ cuspInfinity := QuotientGroup.rightRel_apply.mp hgh
  have := complexPointSeed_cusp E J s (h * g⁻¹) hmem (g • z)
  simpa [mul_smul] using this.symm

def complexPoincareTerm (E : ℂ) (J : ℤ) (s : ℂ) (z : UpperHalfPlane)
    (q : CuspCoset) : ℂ :=
  Quotient.lift (fun g : SL(2, ℤ) => complexPointSeed E J s (g • z))
    (fun _ _ h => complexPointSeed_coset_eq E J s z h) q

@[simp] theorem complexPoincareTerm_mk (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) :
    complexPoincareTerm E J s z (Quotient.mk _ g) =
      complexPointSeed E J s (g • z) := rfl

@[simp] theorem complexPoincareTerm_identity (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) :
    complexPoincareTerm E J s z identityCuspCoset = complexPointSeed E J s z := by
  simp [identityCuspCoset]

theorem complexPoincareTerm_out (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    complexPoincareTerm E J s z q = complexPointSeed E J s (q.out • z) := by
  conv_lhs => rw [← q.out_eq]
  rfl

theorem complexPoincareTerm_smul (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) (q : CuspCoset) :
    complexPoincareTerm E J s (g • z) q =
      complexPoincareTerm E J s z (cuspRightEquiv g q) := by
  induction q using Quotient.inductionOn with | h h =>
    simp [cuspRightEquiv, mul_smul]

def complexPoincareDifferenceTerm (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (q : CuspCoset) : ℂ :=
  complexPoincareTerm E J s z q - complexPoincareTerm 0 J s z q

theorem complexPoincareDifferenceTerm_smul (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) (q : CuspCoset) :
    complexPoincareDifferenceTerm E J s (g • z) q =
      complexPoincareDifferenceTerm E J s z (cuspRightEquiv g q) := by
  simp only [complexPoincareDifferenceTerm, complexPoincareTerm_smul]

@[simp] theorem complexPointSeed_ofReal (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) :
    complexPointSeed E J s z = pointSeed E J s z := by
  unfold complexPointSeed pointSeed
  rw [← Complex.ofReal_cpow z.im_pos.le s]
  push_cast
  rfl

@[simp] theorem complexPoincareTerm_ofReal (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    complexPoincareTerm E J s z q = poincareTerm E J s z q := by
  rw [complexPoincareTerm_out, poincareTerm_out, complexPointSeed_ofReal]

@[simp] theorem complexPoincareDifferenceTerm_ofReal (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    complexPoincareDifferenceTerm E J s z q =
      poincareTerm E J s z q - poincareTerm 0 J s z q := by
  simp only [complexPoincareDifferenceTerm, complexPoincareTerm_ofReal,
    ← Complex.ofReal_zero]

theorem norm_complexPointSeed (E : ℂ) (J : ℤ) (s : ℂ) (z : UpperHalfPlane) :
    ‖complexPointSeed E J s z‖ =
      z.im ^ s.re * Real.exp (-2 * Real.pi * E.re * z.im) := by
  rw [complexPointSeed, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,
    Complex.norm_exp]
  congr 2
  simp

theorem norm_complexPointSeed_le (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) {M : ℝ} (hzM : z.im ≤ M) :
    ‖complexPointSeed E J s z‖ ≤
      Real.exp (2 * Real.pi * ‖E‖ * M) * z.im ^ s.re := by
  rw [norm_complexPointSeed, mul_comm]
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg z.im_pos.le _)
  apply Real.exp_le_exp.mpr
  have hneg : -E.re ≤ ‖E‖ := (neg_le_abs E.re).trans (Complex.abs_re_le_norm E)
  have h₁ : -E.re * z.im ≤ ‖E‖ * M :=
    (mul_le_mul_of_nonneg_right hneg z.im_pos.le).trans
      (mul_le_mul_of_nonneg_left hzM (norm_nonneg E))
  convert mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * Real.pi by positivity) using 1 <;>
    ring

theorem complexPointSeed_sub_zero_energy (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) :
    complexPointSeed E J s z - complexPointSeed 0 J s z =
      (z.im : ℂ) ^ s * Complex.exp
        (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I) *
        (Complex.exp (-2 * (Real.pi : ℂ) * E * z.im) - 1) := by
  simp only [complexPointSeed, mul_zero, zero_mul, zero_add, Complex.exp_add]
  ring

theorem norm_complexPointSeed_sub_zero_energy_le (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) {M : ℝ} (hzM : z.im ≤ M) :
    ‖complexPointSeed E J s z - complexPointSeed 0 J s z‖ ≤
      (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖ * M)) *
        z.im ^ (s.re + 1) := by
  rw [complexPointSeed_sub_zero_energy, norm_mul, norm_mul]
  have hphase : ‖Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hphase, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]
  have hnorm : ‖-2 * (Real.pi : ℂ) * E * z.im‖ = 2 * Real.pi * ‖E‖ * z.im := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos z.im_pos]
  have hexp : ‖Complex.exp (-2 * (Real.pi : ℂ) * E * z.im) - 1‖ ≤
      (2 * Real.pi * ‖E‖ * z.im) * Real.exp (2 * Real.pi * ‖E‖ * z.im) := by
    simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_one, hnorm] using Complex.norm_exp_sub_sum_le_norm_mul_exp
      (-2 * (Real.pi : ℂ) * E * z.im) 1
  have hmono : Real.exp (2 * Real.pi * ‖E‖ * z.im) ≤
      Real.exp (2 * Real.pi * ‖E‖ * M) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzM (by positivity))
  calc
    _ ≤ z.im ^ s.re * ((2 * Real.pi * ‖E‖ * z.im) *
        Real.exp (2 * Real.pi * ‖E‖ * M)) :=
      mul_le_mul_of_nonneg_left
        (hexp.trans (mul_le_mul_of_nonneg_left hmono (by positivity)))
        (Real.rpow_nonneg z.im_pos.le _)
    _ = _ := by rw [Real.rpow_add_one z.im_pos.ne']; ring

theorem norm_complexPoincareDifferenceTerm_le (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    ‖complexPoincareDifferenceTerm E J s z q‖ ≤
      (2 * Real.pi * ‖E‖ *
        Real.exp (2 * Real.pi * ‖E‖ * (z.im / EisensteinSeries.r z ^ 2))) *
        (q.out • z).im ^ (s.re + 1) := by
  simp only [complexPoincareDifferenceTerm, complexPoincareTerm_out]
  exact norm_complexPointSeed_sub_zero_energy_le E J s (q.out • z) (cusp_height_le z q)

theorem differentiable_complexPointSeed_energy (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) : Differentiable ℂ (fun E : ℂ => complexPointSeed E J s z) := by
  unfold complexPointSeed
  fun_prop

theorem differentiable_complexPointSeed_exponent (E : ℂ) (J : ℤ)
    (z : UpperHalfPlane) : Differentiable ℂ (fun s : ℂ => complexPointSeed E J s z) := by
  unfold complexPointSeed
  apply Differentiable.mul_const
  exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr z.im_pos.ne'))

theorem differentiable_complexPointSeed_joint (J : ℤ) (z : UpperHalfPlane) :
    Differentiable ℂ (fun p : ℂ × ℂ => complexPointSeed p.1 J p.2 z) := by
  unfold complexPointSeed
  apply Differentiable.mul
  · exact differentiable_snd.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr z.im_pos.ne'))
  · fun_prop

theorem differentiable_complexPoincareTerm_energy (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    Differentiable ℂ (fun E : ℂ => complexPoincareTerm E J s z q) := by
  simp only [complexPoincareTerm_out]
  exact differentiable_complexPointSeed_energy J s (q.out • z)

theorem differentiable_complexPoincareTerm_exponent (E : ℂ) (J : ℤ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    Differentiable ℂ (fun s : ℂ => complexPoincareTerm E J s z q) := by
  simp only [complexPoincareTerm_out]
  exact differentiable_complexPointSeed_exponent E J (q.out • z)

theorem differentiable_complexPoincareTerm_joint (J : ℤ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    Differentiable ℂ (fun p : ℂ × ℂ => complexPoincareTerm p.1 J p.2 z q) := by
  simp only [complexPoincareTerm_out]
  exact differentiable_complexPointSeed_joint J (q.out • z)

theorem differentiable_complexPoincareDifferenceTerm_energy (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    Differentiable ℂ (fun E : ℂ => complexPoincareDifferenceTerm E J s z q) :=
  (differentiable_complexPoincareTerm_energy J s z q).sub (differentiable_const _)

theorem differentiable_complexPoincareDifferenceTerm_exponent (E : ℂ) (J : ℤ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    Differentiable ℂ (fun s : ℂ => complexPoincareDifferenceTerm E J s z q) :=
  (differentiable_complexPoincareTerm_exponent E J z q).sub
    (differentiable_complexPoincareTerm_exponent 0 J z q)

theorem differentiable_complexPoincareDifferenceTerm_joint (J : ℤ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    Differentiable ℂ (fun p : ℂ × ℂ => complexPoincareDifferenceTerm p.1 J p.2 z q) := by
  apply (differentiable_complexPoincareTerm_joint J z q).sub
  exact (differentiable_complexPoincareTerm_exponent 0 J z q).comp differentiable_snd


/-- Parameter pairs `(E,s)` in the domain of the normally convergent correction. -/
def poincareParameterDomain : Set (ℂ × ℂ) := {p | 0 < p.2.re}

theorem isOpen_poincareParameterDomain : IsOpen poincareParameterDomain :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)

/-- A fixed spatial point bounds every quotient representative's orbit height. -/
def poincareHeightBound (z : UpperHalfPlane) : ℝ := z.im / EisensteinSeries.r z ^ 2

theorem poincareHeightBound_pos (z : UpperHalfPlane) : 0 < poincareHeightBound z :=
  div_pos z.im_pos (sq_pos_of_pos (EisensteinSeries.r_pos z))

/-- Two endpoint exponents bound all real exponents in an interval, for every
positive height, without requiring that the height be below one. -/
theorem rpow_le_add_endpoint {y a b t : ℝ} (hy : 0 < y)
    (hat : a ≤ t) (htb : t ≤ b) : y ^ t ≤ y ^ a + y ^ b := by
  rcases le_total y 1 with hy1 | h1y
  · exact (Real.rpow_le_rpow_of_exponent_ge hy hy1 hat).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h1y htb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le _))

/-- Explicit summable majorant for bounded energies and bounded exponent strips. -/
def poincareParameterMajorant (z : UpperHalfPlane) (a b B : ℝ) (q : CuspCoset) : ℝ :=
  (2 * Real.pi * B * Real.exp (2 * Real.pi * B * poincareHeightBound z)) *
    ((q.out • z).im ^ (a + 1) + (q.out • z).im ^ (b + 1))

theorem summable_poincareParameterMajorant (z : UpperHalfPlane) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (B : ℝ) :
    Summable (poincareParameterMajorant z a b B) :=
  ((summable_cusp_height (s := a + 1) (by linarith) z).add
    (summable_cusp_height (s := b + 1) (by linarith) z)).mul_left _

theorem poincareParameterMajorant_bound (z : UpperHalfPlane) (E s : ℂ)
    {a b B : ℝ} (ha : a ≤ s.re) (hb : s.re ≤ b) (hE : ‖E‖ ≤ B)
    (q : CuspCoset) :
    (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖ * poincareHeightBound z)) *
      (q.out • z).im ^ (s.re + 1) ≤ poincareParameterMajorant z a b B q := by
  have hB : 0 ≤ B := (norm_nonneg E).trans hE
  have hM := (poincareHeightBound_pos z).le
  have hc : 2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖ * poincareHeightBound z) ≤
      2 * Real.pi * B * Real.exp (2 * Real.pi * B * poincareHeightBound z) := by
    gcongr
  exact mul_le_mul hc
    (rpow_le_add_endpoint (q.out • z).im_pos (by linarith) (by linarith))
    (Real.rpow_nonneg (q.out • z).im_pos.le _) (by positivity)

/-- Compact subsets of the complex parameter domain have a positive lower
real-part bound, a finite upper bound, and one bound on input-energy norms. -/
theorem exists_poincareParameter_bounds {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hKD : K ⊆ poincareParameterDomain) :
    ∃ a b B : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ B ∧
      ∀ p ∈ K, a ≤ p.2.re ∧ p.2.re ≤ b ∧ ‖p.1‖ ≤ B := by
  by_cases hne : K.Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne
      (Complex.continuous_re.comp continuous_snd).continuousOn
    obtain ⟨B, hB, hnorm⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨p₀.2.re, B, B, hKD hp₀, hB, hB.le, ?_⟩
    intro p hp
    exact ⟨hmin hp, (Complex.re_le_norm p.2).trans ((norm_snd_le p).trans (hnorm p hp)),
      (norm_fst_le p).trans (hnorm p hp)⟩
  · refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro p hp
    exact (hne ⟨p, hp⟩).elim


/-- A positive lower bound on the Eisenstein denominator gives a uniform orbit-height bound. -/
lemma cusp_height_le_of_mem_verticalStrip {A B Y : ℝ} (hB : 0 < B)
    {z : UpperHalfPlane} (hz : z ∈ UpperHalfPlane.verticalStrip A B) (hY : z.im ≤ Y)
    (q : CuspCoset) :
    (q.out • z).im ≤ Y / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 2 := by
  have hr := EisensteinSeries.r_pos (⟨⟨A, B⟩, hB⟩ : UpperHalfPlane)
  have hrz := EisensteinSeries.r_lower_bound_on_verticalStrip z hB hz
  refine (cusp_height_le z q).trans ?_
  calc
    z.im / EisensteinSeries.r z ^ 2 ≤ z.im / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 2 :=
      div_le_div_of_nonneg_left z.im_pos.le (sq_pos_of_pos hr)
        (pow_le_pow_left₀ hr.le hrz 2)
    _ ≤ Y / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 2 :=
      div_le_div_of_nonneg_right hY (sq_nonneg _)

/-- A single strip/height bound controls every term by an explicit integer-row power. -/
lemma cusp_height_rpow_le_of_mem_verticalStrip {A B Y t : ℝ} (hB : 0 < B)
    (ht : 0 ≤ t) {z : UpperHalfPlane} (hz : z ∈ UpperHalfPlane.verticalStrip A B)
    (hY : z.im ≤ Y) (q : CuspCoset) :
    (q.out • z).im ^ t ≤
      (Y ^ t * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * t))) *
        ‖cuspBottomRow q‖ ^ (-(2 * t)) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  change (z.im / Complex.normSq ((cuspBottomRow q 0 : ℂ) * z + cuspBottomRow q 1)) ^ t ≤ _
  rw [poincare_height_rpow_eq]
  have hden := EisensteinSeries.summand_bound_of_mem_verticalStrip
    (show 0 ≤ 2 * t by positivity) (cuspBottomRow q) hB hz
  calc
    z.im ^ t * ‖(cuspBottomRow q 0 : ℂ) * z + cuspBottomRow q 1‖ ^ (-(2 * t)) ≤
      Y ^ t * (EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * t)) *
        ‖cuspBottomRow q‖ ^ (-(2 * t))) :=
      mul_le_mul (Real.rpow_le_rpow z.im_pos.le hY ht) hden
        (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (z.im_pos.le.trans hY) _)
    _ = _ := by ring

/-- On every compact set, all modular heights are uniformly bounded and their `t` powers
have one summable nonnegative majorant whenever `t > 1`. -/
theorem exists_cusp_height_compact_majorant {K : Set UpperHalfPlane} (hK : IsCompact K)
    {t : ℝ} (ht : 1 < t) :
    ∃ M : ℝ, 0 < M ∧ ∃ u : CuspCoset → ℝ,
      Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (z : UpperHalfPlane), z ∈ K →
        (q.out • z).im ≤ M ∧ (q.out • z).im ^ t ≤ u q := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · refine ⟨1, zero_lt_one, 0, summable_zero, fun _ => le_rfl, ?_⟩
    simp
  obtain ⟨zmax, hzmax, hmax⟩ :=
    hK.exists_isMaxOn hne UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨A, B, hB, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  let ρ : ℝ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩
  have hρ : 0 < ρ := EisensteinSeries.r_pos _
  refine ⟨zmax.im / ρ ^ 2, div_pos zmax.im_pos (sq_pos_of_pos hρ),
    fun q => (zmax.im ^ t * ρ ^ (-(2 * t))) * ‖cuspBottomRow q‖ ^ (-(2 * t)), ?_,
    fun q => by positivity, ?_⟩
  · exact ((EisensteinSeries.summable_one_div_norm_rpow (show 2 < 2 * t by linarith)).comp_injective cuspBottomRow_injective).mul_left _
  · intro q z hz
    exact ⟨cusp_height_le_of_mem_verticalStrip hB (hstrip hz) (hmax hz) q,
      cusp_height_rpow_le_of_mem_verticalStrip hB (by linarith) (hstrip hz) (hmax hz) q⟩


/-- Actual complex energy correction on the original cusp quotient. -/
def complexPoincareEnergyDifference (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) : ℂ :=
  ∑' q : CuspCoset, complexPoincareDifferenceTerm E J s z q

/-- The original point series with complex energy and convergence exponent. -/
def complexPoincareSeries (E : ℂ) (J : ℤ) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' q : CuspCoset, complexPoincareTerm E J s z q

@[simp] theorem complexPoincareSeries_ofReal (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) : complexPoincareSeries E J s z = poincareSeries E J s z := by
  simp only [complexPoincareSeries, complexPoincareTerm_ofReal, poincareSeries]

theorem summable_norm_complexPoincareTerm (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable fun q : CuspCoset => ‖complexPoincareTerm E J s z q‖ := by
  apply ((summable_cusp_height hs z).mul_left
    (Real.exp (2 * Real.pi * ‖E‖ * poincareHeightBound z))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro q
  rw [complexPoincareTerm_out]
  exact norm_complexPointSeed_le E J s (q.out • z) (cusp_height_le z q)

theorem hasSum_complexPoincareTerm (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (z : UpperHalfPlane) :
    HasSum (complexPoincareTerm E J s z) (complexPoincareSeries E J s z) :=
  (summable_norm_complexPoincareTerm E J hs z).of_norm.hasSum

theorem complexPoincareSeries_smul (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) :
    complexPoincareSeries E J s (g • z) = complexPoincareSeries E J s z := by
  simp only [complexPoincareSeries, complexPoincareTerm_smul]
  exact (cuspRightEquiv g).tsum_eq (complexPoincareTerm E J s z)

/-- The analytic correction is the actual difference of the two original complex
Poincaré sums throughout their common convergence region. -/
theorem complexPoincareEnergyDifference_eq_sub (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (z : UpperHalfPlane) :
    complexPoincareEnergyDifference E J s z =
      complexPoincareSeries E J s z - complexPoincareSeries 0 J s z :=
  (summable_norm_complexPoincareTerm E J hs z).of_norm.tsum_sub
    (summable_norm_complexPoincareTerm 0 J hs z).of_norm

@[simp] theorem complexPoincareEnergyDifference_ofReal (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) :
    complexPoincareEnergyDifference E J s z = poincareEnergyDifference E J s z := by
  simp only [complexPoincareEnergyDifference, complexPoincareDifferenceTerm_ofReal,
    poincareEnergyDifference]

theorem complexPoincareEnergyDifference_smul (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) :
    complexPoincareEnergyDifference E J s (g • z) = complexPoincareEnergyDifference E J s z := by
  simp only [complexPoincareEnergyDifference, complexPoincareDifferenceTerm_smul]
  exact (cuspRightEquiv g).tsum_eq (complexPoincareDifferenceTerm E J s z)

theorem norm_complexPoincareDifferenceTerm_le_majorant (E s : ℂ) (J : ℤ)
    (z : UpperHalfPlane) {a b B : ℝ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    (hE : ‖E‖ ≤ B) (q : CuspCoset) :
    ‖complexPoincareDifferenceTerm E J s z q‖ ≤ poincareParameterMajorant z a b B q := by
  apply le_trans _ (poincareParameterMajorant_bound z E s ha hb hE q)
  unfold complexPoincareDifferenceTerm
  rw [complexPoincareTerm_out, complexPoincareTerm_out]
  exact norm_complexPointSeed_sub_zero_energy_le E J s (q.out • z) (cusp_height_le z q)

/-- A single summable majorant works uniformly on each compact complex parameter set. -/
theorem complexPoincareDifferenceTerm_normal_on_compact (J : ℤ) (z : UpperHalfPlane)
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (hKD : K ⊆ poincareParameterDomain) :
    ∃ u : CuspCoset → ℝ, Summable u ∧
      ∀ q p, p ∈ K → ‖complexPoincareDifferenceTerm p.1 J p.2 z q‖ ≤ u q := by
  obtain ⟨a, b, B, ha, hb, _, hbound⟩ := exists_poincareParameter_bounds hK hKD
  refine ⟨poincareParameterMajorant z a b B,
    summable_poincareParameterMajorant z ha hb B, ?_⟩
  intro q p hp
  obtain ⟨hp₁, hp₂, hp₃⟩ := hbound p hp
  exact norm_complexPoincareDifferenceTerm_le_majorant p.1 p.2 J z hp₁ hp₂ hp₃ q

/-- One summable majorant controls compact energy/exponent sets and compact spatial
sets simultaneously, uniformly in the integer spin. -/
theorem complexPoincareDifferenceTerm_normal_on_compact_product
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (hKD : K ⊆ poincareParameterDomain)
    {L : Set UpperHalfPlane} (hL : IsCompact L) :
    ∃ u : CuspCoset → ℝ, Summable u ∧
      ∀ (J : ℤ) q p z, p ∈ K → z ∈ L →
        ‖complexPoincareDifferenceTerm p.1 J p.2 z q‖ ≤ u q := by
  obtain ⟨a, b, B, ha, hb, hB, hbound⟩ := exists_poincareParameter_bounds hK hKD
  obtain ⟨M, hM, u, hu, hu0, hqu⟩ :=
    exists_cusp_height_compact_majorant hL (t := a + 1) (by linarith)
  obtain ⟨_, _, v, hv, hv0, hqv⟩ :=
    exists_cusp_height_compact_majorant hL (t := b + 1) (by linarith)
  let C : ℝ := 2 * Real.pi * B * Real.exp (2 * Real.pi * B * M)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨fun q => C * (u q + v q), (hu.add hv).mul_left C, ?_⟩
  intro J q p z hp hz
  obtain ⟨hp₁, hp₂, hp₃⟩ := hbound p hp
  have hcoeff : 2 * Real.pi * ‖p.1‖ * Real.exp (2 * Real.pi * ‖p.1‖ * M) ≤ C := by
    dsimp [C]
    gcongr
  have hpowers : (q.out • z).im ^ (p.2.re + 1) ≤ u q + v q :=
    (rpow_le_add_endpoint (q.out • z).im_pos (by linarith) (by linarith)).trans
      (add_le_add (hqu q z hz).2 (hqv q z hz).2)
  apply le_trans _ (mul_le_mul hcoeff hpowers
    (Real.rpow_nonneg (q.out • z).im_pos.le _) hC)
  unfold complexPoincareDifferenceTerm
  rw [complexPoincareTerm_out, complexPoincareTerm_out]
  exact norm_complexPointSeed_sub_zero_energy_le p.1 J p.2 (q.out • z) (hqu q z hz).1

/-- Compact normal convergence when the spatial point also varies. -/
theorem complexPoincareDifferenceTerm_normal_on_compact_full
    {K : Set ((ℂ × ℂ) × UpperHalfPlane)} (hK : IsCompact K)
    (hKD : ∀ p ∈ K, 0 < p.1.2.re) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ ∀ (J : ℤ) q p, p ∈ K →
      ‖complexPoincareDifferenceTerm p.1.1 J p.1.2 p.2 q‖ ≤ u q := by
  have hfst : Prod.fst '' K ⊆ poincareParameterDomain := by
    rintro p ⟨w, hw, rfl⟩
    exact hKD w hw
  obtain ⟨u, hu, hbound⟩ := complexPoincareDifferenceTerm_normal_on_compact_product
    (hK.image continuous_fst) hfst (hK.image continuous_snd)
  exact ⟨u, hu, fun J q p hp => hbound J q p.1 p.2
    (mem_image_of_mem _ hp) (mem_image_of_mem _ hp)⟩

/-- The actual correction partial sums converge locally uniformly in the complex
energy, complex exponent, and spatial point throughout `re s > 0`. -/
theorem complexPoincareEnergyDifference_tendstoLocallyUniformlyOn_full (J : ℤ) :
    TendstoLocallyUniformlyOn
      (fun A : Finset CuspCoset => fun p : (ℂ × ℂ) × UpperHalfPlane =>
        ∑ q ∈ A, complexPoincareDifferenceTerm p.1.1 J p.1.2 p.2 q)
      (fun p => complexPoincareEnergyDifference p.1.1 J p.1.2 p.2) atTop
      {p | 0 < p.1.2.re} := by
  have hopen : IsOpen {p : (ℂ × ℂ) × UpperHalfPlane | 0 < p.1.2.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.comp continuous_fst))
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKD hK
  obtain ⟨u, hu, hbound⟩ := complexPoincareDifferenceTerm_normal_on_compact_full hK
    (fun p hp => hKD hp)
  exact tendstoUniformlyOn_tsum hu (hbound J)

/-- Absolute convergence in the full complex half-plane `re s > 0`. -/
theorem summable_norm_complexPoincareDifferenceTerm (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 0 < s.re) (z : UpperHalfPlane) :
    Summable fun q : CuspCoset => ‖complexPoincareDifferenceTerm E J s z q‖ := by
  exact (summable_poincareParameterMajorant z hs hs ‖E‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_complexPoincareDifferenceTerm_le_majorant E s J z
      le_rfl le_rfl le_rfl)

theorem hasSum_complexPoincareEnergyDifference (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 0 < s.re) (z : UpperHalfPlane) :
    HasSum (complexPoincareDifferenceTerm E J s z) (complexPoincareEnergyDifference E J s z) :=
  (summable_norm_complexPoincareDifferenceTerm E J hs z).of_norm.hasSum

/-- The actual quotient partial sums converge jointly uniformly on compact parameter sets. -/
theorem complexPoincareEnergyDifference_tendstoUniformlyOn_compact (J : ℤ)
    (z : UpperHalfPlane) {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hKD : K ⊆ poincareParameterDomain) :
    TendstoUniformlyOn
      (fun A : Finset CuspCoset => fun p : ℂ × ℂ =>
        ∑ q ∈ A, complexPoincareDifferenceTerm p.1 J p.2 z q)
      (fun p => complexPoincareEnergyDifference p.1 J p.2 z) atTop K := by
  obtain ⟨u, hu, hbound⟩ := complexPoincareDifferenceTerm_normal_on_compact J z hK hKD
  exact tendstoUniformlyOn_tsum hu hbound

/-- Joint local normal convergence throughout the complex parameter domain. -/
theorem complexPoincareEnergyDifference_tendstoLocallyUniformlyOn (J : ℤ)
    (z : UpperHalfPlane) :
    TendstoLocallyUniformlyOn
      (fun A : Finset CuspCoset => fun p : ℂ × ℂ =>
        ∑ q ∈ A, complexPoincareDifferenceTerm p.1 J p.2 z q)
      (fun p => complexPoincareEnergyDifference p.1 J p.2 z) atTop poincareParameterDomain := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_poincareParameterDomain]
  exact fun K hKD hK => complexPoincareEnergyDifference_tendstoUniformlyOn_compact J z hK hKD

/-- The correction is holomorphic along every holomorphic parameter curve staying
inside `re s > 0`. In particular energy is entire and the exponent is holomorphic. -/
theorem differentiableOn_complexPoincareEnergyDifference_comp (J : ℤ) (z : UpperHalfPlane)
    {U : Set ℂ} (hU : IsOpen U) (E s : ℂ → ℂ)
    (hE : DifferentiableOn ℂ E U) (hs : DifferentiableOn ℂ s U)
    (hpos : ∀ t ∈ U, 0 < (s t).re) :
    DifferentiableOn ℂ (fun t => complexPoincareEnergyDifference (E t) J (s t) z) U := by
  have hpair : DifferentiableOn ℂ (fun t => (E t, s t)) U := hE.prodMk hs
  have hlim := (complexPoincareEnergyDifference_tendstoLocallyUniformlyOn J z).comp
    (fun t => (E t, s t)) hpos hpair.continuousOn
  apply hlim.differentiableOn _ hU
  apply Filter.Eventually.of_forall
  intro A
  exact DifferentiableOn.fun_sum fun q _ =>
    (differentiable_complexPoincareDifferenceTerm_joint J z q).comp_differentiableOn hpair

theorem differentiable_complexPoincareEnergyDifference_energy (J : ℤ) {s : ℂ}
    (hs : 0 < s.re) (z : UpperHalfPlane) :
    Differentiable ℂ (fun E : ℂ => complexPoincareEnergyDifference E J s z) := by
  apply differentiableOn_univ.mp
  exact differentiableOn_complexPoincareEnergyDifference_comp J z isOpen_univ
    id (fun _ => s) differentiable_id.differentiableOn
    (differentiable_const s).differentiableOn (fun _ _ => hs)

theorem complexPoincareEnergyDifference_analyticAt_energy (J : ℤ) {s : ℂ}
    (hs : 0 < s.re) (z : UpperHalfPlane) (E : ℂ) :
    AnalyticAt ℂ (fun E : ℂ => complexPoincareEnergyDifference E J s z) E :=
  (differentiable_complexPoincareEnergyDifference_energy J hs z).analyticAt E

theorem differentiableOn_complexPoincareEnergyDifference_exponent (E : ℂ) (J : ℤ)
    (z : UpperHalfPlane) :
    DifferentiableOn ℂ (fun s : ℂ => complexPoincareEnergyDifference E J s z) {s | 0 < s.re} :=
  differentiableOn_complexPoincareEnergyDifference_comp J z
    (isOpen_lt continuous_const Complex.continuous_re) (fun _ => E) id
    (differentiable_const E).differentiableOn differentiable_id.differentiableOn
    (fun _ h => h)

theorem complexPoincareEnergyDifference_analyticAt_exponent (E : ℂ) (J : ℤ)
    (z : UpperHalfPlane) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun s : ℂ => complexPoincareEnergyDifference E J s z) s :=
  (differentiableOn_complexPoincareEnergyDifference_exponent E J z).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)


/-- Positive energies improve the subtraction bound from exponential to linear growth. -/
theorem norm_pointSeed_sub_zero_energy_le_of_nonneg {E : ℝ} (hE : 0 ≤ E)
    (J : ℤ) (s : ℝ) (z : UpperHalfPlane) :
    ‖pointSeed E J s z - pointSeed 0 J s z‖ ≤
      (2 * Real.pi * E) * z.im ^ (s + 1) := by
  rw [pointSeed_sub_zero_energy, norm_mul, norm_mul]
  have hphase : ‖Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hphase, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _)]
  have hnonpos : -2 * Real.pi * E * z.im ≤ 0 := by
    have : 0 ≤ 2 * Real.pi * E * z.im := by positivity
    linarith
  have hexp_le : Real.exp (-2 * Real.pi * E * z.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr hnonpos
  have hnorm : ‖Complex.exp (((-2 * Real.pi * E * z.im : ℝ) : ℂ)) - 1‖ =
      1 - Real.exp (-2 * Real.pi * E * z.im) := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hexp_le)]
    ring
  rw [hnorm]
  have hexp : 1 - Real.exp (-2 * Real.pi * E * z.im) ≤
      2 * Real.pi * E * z.im := by
    have := Real.add_one_le_exp (-2 * Real.pi * E * z.im)
    linarith
  calc
    _ ≤ z.im ^ s * (2 * Real.pi * E * z.im) :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg z.im_pos.le _)
    _ = _ := by rw [Real.rpow_add_one z.im_pos.ne']; ring

/-- The actual convergent energy correction has uniform linear growth in nonnegative
energy, with a coefficient independent of spin. -/
theorem norm_poincareEnergyDifference_le_of_nonneg {E : ℝ} (hE : 0 ≤ E)
    (J : ℤ) {s : ℝ} (hs : 0 < s) (z : UpperHalfPlane) :
    ‖poincareEnergyDifference E J s z‖ ≤
      (2 * Real.pi * ∑' q : CuspCoset, (q.out • z).im ^ (s + 1)) * E := by
  have hheight := summable_cusp_height (s := s + 1) (by linarith) z
  calc
    _ ≤ ∑' q : CuspCoset, ‖poincareTerm E J s z q - poincareTerm 0 J s z q‖ :=
      norm_tsum_le_tsum_norm (summable_norm_poincareTerm_sub_zero E J hs z)
    _ ≤ ∑' q : CuspCoset, (2 * Real.pi * E) * (q.out • z).im ^ (s + 1) := by
      apply Summable.tsum_le_tsum _ (summable_norm_poincareTerm_sub_zero E J hs z)
        (hheight.mul_left _)
      intro q
      rw [poincareTerm_out, poincareTerm_out]
      exact norm_pointSeed_sub_zero_energy_le_of_nonneg hE J s (q.out • z)
    _ = _ := by rw [tsum_mul_left]; ring

private theorem abs_exp_neg_sub_exp_neg_le_aux {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ y - x := by
  have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hd : 0 ≤ 1 - Real.exp (-(y - x)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hd' : 1 - Real.exp (-(y - x)) ≤ y - x := by
    linarith [Real.one_sub_le_exp_neg (y - x)]
  have hfac : Real.exp (-x) - Real.exp (-y) =
      Real.exp (-x) * (1 - Real.exp (-(y - x))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  rw [hfac, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hd)]
  exact (mul_le_of_le_one_left hd he).trans hd'

/-- Real exponential decay is a contraction on the positive half-line. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  rcases le_total x y with hxy | hyx
  · simpa [abs_of_nonpos (sub_nonpos.mpr hxy)] using
      abs_exp_neg_sub_exp_neg_le_aux hx hxy
  · rw [abs_sub_comm (Real.exp (-x)), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact abs_exp_neg_sub_exp_neg_le_aux hy hyx

/-- At fixed spin, seeds vary at most linearly between any two nonnegative energies. -/
theorem norm_pointSeed_sub_le_of_nonneg {E F : ℝ} (hE : 0 ≤ E) (hF : 0 ≤ F)
    (J : ℤ) (s : ℝ) (z : UpperHalfPlane) :
    ‖pointSeed E J s z - pointSeed F J s z‖ ≤
      (2 * Real.pi * |E - F|) * z.im ^ (s + 1) := by
  have hfac : pointSeed E J s z - pointSeed F J s z =
      (z.im ^ s : ℝ) * Complex.exp
        (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I) *
        ((Real.exp (-2 * Real.pi * E * z.im) -
          Real.exp (-2 * Real.pi * F * z.im) : ℝ) : ℂ) := by
    simp only [pointSeed, Complex.exp_add, Complex.ofReal_sub, Complex.ofReal_exp]
    ring
  rw [hfac, norm_mul, norm_mul]
  have hphase : ‖Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hphase, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _), Complex.norm_real,
    Real.norm_eq_abs]
  have hexp := abs_exp_neg_sub_exp_neg_le (x := 2 * Real.pi * E * z.im)
    (y := 2 * Real.pi * F * z.im) (by positivity) (by positivity)
  have harg : 2 * Real.pi * E * z.im - 2 * Real.pi * F * z.im =
      (2 * Real.pi * z.im) * (E - F) := by ring
  rw [harg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi * z.im)] at hexp
  simp only [← neg_mul] at hexp
  calc
    _ ≤ z.im ^ s * ((2 * Real.pi * z.im) * |E - F|) :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg z.im_pos.le _)
    _ = _ := by rw [Real.rpow_add_one z.im_pos.ne']; ring

/-- The correction is Lipschitz in nonnegative energy with a spin-independent
coefficient given by a genuinely convergent Eisenstein majorant. -/
theorem norm_poincareEnergyDifference_sub_le_of_nonneg {E F : ℝ}
    (hE : 0 ≤ E) (hF : 0 ≤ F) (J : ℤ) {s : ℝ} (hs : 0 < s)
    (z : UpperHalfPlane) :
    ‖poincareEnergyDifference E J s z - poincareEnergyDifference F J s z‖ ≤
      (2 * Real.pi * ∑' q : CuspCoset, (q.out • z).im ^ (s + 1)) * |E - F| := by
  have hheight := summable_cusp_height (s := s + 1) (by linarith) z
  have hmajor := hheight.mul_left (2 * Real.pi * |E - F|)
  have hbound (q : CuspCoset) :
      ‖poincareTerm E J s z q - poincareTerm F J s z q‖ ≤
        (2 * Real.pi * |E - F|) * (q.out • z).im ^ (s + 1) := by
    rw [poincareTerm_out, poincareTerm_out]
    exact norm_pointSeed_sub_le_of_nonneg hE hF J s (q.out • z)
  have hsum : Summable (fun q : CuspCoset =>
      ‖poincareTerm E J s z q - poincareTerm F J s z q‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have heq : poincareEnergyDifference E J s z - poincareEnergyDifference F J s z =
      ∑' q : CuspCoset, (poincareTerm E J s z q - poincareTerm F J s z q) := by
    rw [poincareEnergyDifference, poincareEnergyDifference,
      ← (summable_norm_poincareTerm_sub_zero E J hs z).of_norm.tsum_sub
        (summable_norm_poincareTerm_sub_zero F J hs z).of_norm]
    congr 1
    funext q
    ring
  rw [heq]
  calc
    _ ≤ ∑' q : CuspCoset, ‖poincareTerm E J s z q - poincareTerm F J s z q‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' q : CuspCoset, (2 * Real.pi * |E - F|) * (q.out • z).im ^ (s + 1) :=
      Summable.tsum_le_tsum hbound hsum hmajor
    _ = _ := by rw [tsum_mul_left]; ring

/-- Positive-energy corrections have one spin-independent Lipschitz constant on
every compact spatial set, at each fixed positive real exponent. -/
theorem exists_poincareEnergyDifference_compact_lipschitz
    {K : Set UpperHalfPlane} (hK : IsCompact K) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) z, z ∈ K → ∀ E F : ℝ, 0 ≤ E → 0 ≤ F →
      ‖poincareEnergyDifference E J s z - poincareEnergyDifference F J s z‖ ≤ C * |E - F| := by
  obtain ⟨_, _, u, hu, hu0, hbound⟩ :=
    exists_cusp_height_compact_majorant hK (t := s + 1) (by linarith)
  have hsum0 : 0 ≤ ∑' q, u q := tsum_nonneg hu0
  refine ⟨2 * Real.pi * ∑' q, u q + 1, by positivity, ?_⟩
  intro J z hz E F hE hF
  apply (norm_poincareEnergyDifference_sub_le_of_nonneg hE hF J hs z).trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hsum := Summable.tsum_le_tsum (fun q => (hbound q z hz).2)
    (summable_cusp_height (s := s + 1) (by linarith) z) hu
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * Real.pi by positivity)
  linarith

/-- In particular the correction is locally `O(E)`, and hence `O(1+E)`, on the
whole positive energy ray, uniformly in integer spin. -/
theorem exists_poincareEnergyDifference_compact_linear
    {K : Set UpperHalfPlane} (hK : IsCompact K) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) z, z ∈ K → ∀ E : ℝ, 0 ≤ E →
      ‖poincareEnergyDifference E J s z‖ ≤ C * E := by
  obtain ⟨C, hC, hbound⟩ := exists_poincareEnergyDifference_compact_lipschitz hK hs
  refine ⟨C, hC, ?_⟩
  intro J z hz E hE
  have hzero : poincareEnergyDifference 0 J s z = 0 := by
    simp [poincareEnergyDifference]
  simpa only [hzero, sub_zero, abs_of_nonneg hE] using hbound J z hz E 0 hE le_rfl


end

end GapFamily.Analytic
