import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The point-seed Poincaré series in its convergent region

The cusp subgroup in `SL(2, ℤ)` contains both signs of every translation.
Its left quotient therefore implements `Γ∞ \ PSL(2, ℤ)` without counting
the two matrix signs twice. All series below use that actual quotient.
-/

namespace GapFamily.Analytic

open Complex Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Real UpperHalfPlane

noncomputable section

/-- The inverse image of the translation cusp subgroup of `PSL(2, ℤ)`. -/
def cuspInfinity : Subgroup SL(2, ℤ) where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a 1 0 = 0 at ha
    change b 1 0 = 0 at hb
    change ((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0
    simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  inv_mem' := by
    intro a ha
    change a 1 0 = 0 at ha
    change (↑(a⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0
    simp [coe_inv, Matrix.adjugate_fin_two, ha]

/-- The left quotient by the translation subgroup, with matrix signs identified. -/
abbrev CuspCoset := Quotient (QuotientGroup.rightRel cuspInfinity)

/-- The identity coset, which contributes the original point seed. -/
def identityCuspCoset : CuspCoset := Quotient.mk _ (1 : SL(2, ℤ))

/-- The uncompleted seed; the exponent `s` is real at this stage. -/
def pointSeed (E : ℝ) (J : ℤ) (s : ℝ) (z : UpperHalfPlane) : ℂ :=
  (z.im ^ s : ℝ) * Complex.exp
    (((-2 * Real.pi * E * z.im : ℝ) : ℂ) +
      ((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I)

theorem pointSeed_translation (E : ℝ) (J : ℤ) (s : ℝ)
    (n : ℤ) (z : UpperHalfPlane) :
    pointSeed E J s (ModularGroup.T ^ n • z) = pointSeed E J s z := by
  unfold pointSeed
  rw [ModularGroup.im_T_zpow_smul, ModularGroup.re_T_zpow_smul]
  congr 1
  have harg :
      ((-2 * Real.pi * E * z.im : ℝ) : ℂ) +
          ((2 * Real.pi * (J : ℝ) * (z.re + n) : ℝ) : ℂ) * I =
        (((-2 * Real.pi * E * z.im : ℝ) : ℂ) +
          ((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I) +
          ((J * n : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem pointSeed_cusp (E : ℝ) (J : ℤ) (s : ℝ)
    (g : SL(2, ℤ)) (hg : g ∈ cuspInfinity) (z : UpperHalfPlane) :
    pointSeed E J s (g • z) = pointSeed E J s z := by
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hg
  rw [hn, pointSeed_translation]

/-- Independence of the matrix representative of a cusp coset. -/
theorem pointSeed_coset_eq (E : ℝ) (J : ℤ) (s : ℝ) (z : UpperHalfPlane)
    {g h : SL(2, ℤ)} (hgh : QuotientGroup.rightRel cuspInfinity g h) :
    pointSeed E J s (g • z) = pointSeed E J s (h • z) := by
  have hmem : h * g⁻¹ ∈ cuspInfinity := QuotientGroup.rightRel_apply.mp hgh
  have := pointSeed_cusp E J s (h * g⁻¹) hmem (g • z)
  simpa [mul_smul] using this.symm

/-- The actual seed on the coset space. -/
def poincareTerm (E : ℝ) (J : ℤ) (s : ℝ) (z : UpperHalfPlane)
    (q : CuspCoset) : ℂ :=
  Quotient.lift (fun g : SL(2, ℤ) => pointSeed E J s (g • z))
    (fun _ _ h => pointSeed_coset_eq E J s z h) q

@[simp] theorem poincareTerm_mk (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) :
    poincareTerm E J s z (Quotient.mk _ g) = pointSeed E J s (g • z) := rfl

@[simp] theorem poincareTerm_identity (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) :
    poincareTerm E J s z identityCuspCoset = pointSeed E J s z := by
  simp [identityCuspCoset]

/-- The Poincaré sum. Absolute convergence is proved below before it is used. -/
def poincareSeries (E : ℝ) (J : ℤ) (s : ℝ) (z : UpperHalfPlane) : ℂ :=
  ∑' q : CuspCoset, poincareTerm E J s z q

/-- Right multiplication permutes the left-action cusp quotient. -/
def cuspRightEquiv (g : SL(2, ℤ)) : CuspCoset ≃ CuspCoset where
  toFun := Quotient.map (fun h => h * g) (by
    intro a b hab
    change QuotientGroup.rightRel cuspInfinity a b at hab
    change QuotientGroup.rightRel cuspInfinity (a * g) (b * g)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab)
  invFun := Quotient.map (fun h => h * g⁻¹) (by
    intro a b hab
    change QuotientGroup.rightRel cuspInfinity a b at hab
    change QuotientGroup.rightRel cuspInfinity (a * g⁻¹) (b * g⁻¹)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using hab)
  left_inv q := by
    induction q using Quotient.inductionOn with | h h =>
      simp [mul_assoc]
  right_inv q := by
    induction q using Quotient.inductionOn with | h h =>
      simp [mul_assoc]

theorem poincareTerm_smul (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) (q : CuspCoset) :
    poincareTerm E J s (g • z) q =
      poincareTerm E J s z (cuspRightEquiv g q) := by
  induction q using Quotient.inductionOn with | h h =>
    simp [cuspRightEquiv, mul_smul]

/-- Modularity follows from a permutation of the actual cosets. This is an
identity of totalized sums; `hasSum_poincareTerm` supplies convergence for `s > 1`. -/
theorem poincareSeries_smul (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) :
    poincareSeries E J s (g • z) = poincareSeries E J s z := by
  simp only [poincareSeries, poincareTerm_smul]
  exact (cuspRightEquiv g).tsum_eq _

theorem norm_pointSeed (E : ℝ) (J : ℤ) (s : ℝ) (z : UpperHalfPlane) :
    ‖pointSeed E J s z‖ = z.im ^ s * Real.exp (-2 * Real.pi * E * z.im) := by
  simp [pointSeed, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg z.im_pos.le s), Complex.norm_exp]

private theorem cuspRel_of_bottomRow_eq {g h : SL(2, ℤ)} (heq : g 1 = h 1) :
    QuotientGroup.rightRel cuspInfinity g h := by
  rw [QuotientGroup.rightRel_apply]
  change (↑(h * g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0
  simp only [coe_mul, coe_inv, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← congrFun heq 0, ← congrFun heq 1]
  ring

/-- Two matrices label the same cusp coset exactly when their primitive lower
rows agree up to simultaneous sign. -/
theorem cuspRel_iff_bottomRow (g h : SL(2, ℤ)) :
    QuotientGroup.rightRel cuspInfinity g h ↔ g 1 = h 1 ∨ g 1 = -h 1 := by
  constructor
  · intro hrel
    let k : SL(2, ℤ) := h * g⁻¹
    have hk : k 1 0 = 0 := QuotientGroup.rightRel_apply.mp hrel
    have hdet := k.det_coe
    rw [Matrix.det_fin_two, hk, mul_zero, sub_zero] at hdet
    have hkg : k * g = h := by simp [k, mul_assoc]
    have hrow (i : Fin 2) : h 1 i = k 1 1 * g 1 i := by
      rw [← hkg]
      simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hk]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with (⟨_, hk1⟩ | ⟨_, hk1⟩)
    · left
      funext i
      simpa [hk1] using (hrow i).symm
    · right
      funext i
      simp only [Pi.neg_apply, hrow, hk1, neg_mul, one_mul, neg_neg]
  · rintro (heq | heq)
    · exact cuspRel_of_bottomRow_eq heq
    · rw [QuotientGroup.rightRel_apply]
      change (↑(h * g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0
      simp only [coe_mul, coe_inv, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [congrFun heq 0, congrFun heq 1]
      simp only [Pi.neg_apply]
      ring

/-- Each primitive integer row occurs as the lower row of a matrix representative. -/
theorem primitiveRow_has_representative (v : Fin 2 → ℤ)
    (hv : IsCoprime (v 0) (v 1)) :
    ∃ g : SL(2, ℤ), g 1 = v := by
  obtain ⟨g, _, hg⟩ := ModularGroup.bottom_row_surj hv
  exact ⟨g, hg⟩

/-- A selected lower row for each coset. Its sign need not be normalized. -/
def cuspBottomRow (q : CuspCoset) : Fin 2 → ℤ := q.out 1

/-- Distinct cosets cannot have identical selected lower rows. -/
theorem cuspBottomRow_injective : Function.Injective cuspBottomRow := by
  intro q r hqr
  apply Quotient.out_equiv_out.mp
  exact cuspRel_of_bottomRow_eq hqr

theorem cuspBottomRow_coprime (q : CuspCoset) :
    IsCoprime (cuspBottomRow q 0) (cuspBottomRow q 1) :=
  ModularGroup.bottom_row_coprime q.out

theorem cuspBottomRow_ne_zero (q : CuspCoset) : cuspBottomRow q ≠ 0 := by
  intro hzero
  have h := cuspBottomRow_coprime q
  rw [hzero] at h
  norm_num [IsCoprime] at h

theorem poincareTerm_out (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) (q : CuspCoset) :
    poincareTerm E J s z q = pointSeed E J s (q.out • z) := by
  conv_lhs => rw [← q.out_eq]
  rfl


lemma summable_poincare_denominator (z : ℍ) {s : ℝ} (hs : 1 < s) :
    Summable fun v : Fin 2 → ℤ => ‖(v 0 : ℂ) * z + v 1‖ ^ (-(2 * s)) := by
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun v => EisensteinSeries.summand_bound z (by linarith : 0 ≤ 2 * s) v)
  exact (EisensteinSeries.summable_one_div_norm_rpow (by linarith : 2 < 2 * s)).mul_left _

lemma poincare_height_rpow_eq (z : ℍ) (v : Fin 2 → ℤ) (s : ℝ) :
    (z.im / Complex.normSq ((v 0 : ℂ) * z + v 1)) ^ s =
      z.im ^ s * ‖(v 0 : ℂ) * z + v 1‖ ^ (-(2 * s)) := by
  rw [Real.div_rpow z.im_pos.le (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
    ← Real.rpow_natCast_mul (norm_nonneg _), div_eq_mul_inv,
    ← Real.rpow_neg (norm_nonneg _)]
  norm_num

lemma summable_poincare_height (z : ℍ) {s : ℝ} (hs : 1 < s) :
    Summable fun v : Fin 2 → ℤ =>
      (z.im / Complex.normSq ((v 0 : ℂ) * z + v 1)) ^ s := by
  simpa only [poincare_height_rpow_eq] using
    (summable_poincare_denominator z hs).mul_left (z.im ^ s)

lemma summable_poincare_height_comp {ι : Type*} (z : ℍ) {s : ℝ} (hs : 1 < s)
    (v : ι → Fin 2 → ℤ) (hv : Function.Injective v) :
    Summable fun i : ι =>
      (z.im / Complex.normSq ((v i 0 : ℂ) * z + v i 1)) ^ s :=
  (summable_poincare_height z hs).comp_injective hv


lemma one_le_norm_int_pair (v : Fin 2 → ℤ) (hv : v ≠ 0) : 1 ≤ ‖v‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  have hn : 0 < max (v 0).natAbs (v 1).natAbs := by
    by_contra! hn
    apply hv
    funext i
    fin_cases i <;> simp_all [Int.natAbs_eq_zero]
  norm_cast

lemma poincare_height_le (z : ℍ) (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    z.im / Complex.normSq ((v 0 : ℂ) * z + v 1) ≤ z.im / EisensteinSeries.r z ^ 2 := by
  have hr := EisensteinSeries.r_pos z
  have hden : EisensteinSeries.r z ≤ ‖(v 0 : ℂ) * z + v 1‖ := by
    exact le_trans (le_mul_of_one_le_right hr.le (one_le_norm_int_pair v hv))
      (EisensteinSeries.r_mul_max_le z hv)
  rw [Complex.normSq_eq_norm_sq]
  exact div_le_div_of_nonneg_left z.im_pos.le (sq_pos_of_pos hr)
    (pow_le_pow_left₀ hr.le hden 2)


lemma norm_poincare_seed_bound (E s t : ℝ) {h M : ℝ}
    (hh : 0 ≤ h) (hM : h ≤ M) :
    ‖(h ^ s : ℝ) * Complex.exp (((-2 * Real.pi * E * h : ℝ) : ℂ) +
        (t : ℂ) * Complex.I)‖ ≤
      Real.exp (2 * Real.pi * |E| * M) * h ^ s := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hh _),
    Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hh _)
  apply Real.exp_le_exp.mpr
  have h₁ : -E * h ≤ |E| * M :=
    (mul_le_mul_of_nonneg_right (neg_le_abs E) hh).trans
      (mul_le_mul_of_nonneg_left hM (abs_nonneg E))
  convert mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * Real.pi by positivity) using 1 <;> ring

lemma summable_poincare_seed_comp {ι : Type*} (z : ℍ) {s : ℝ} (hs : 1 < s)
    (E : ℝ) (v : ι → Fin 2 → ℤ) (hv : Function.Injective v)
    (hne : ∀ i, v i ≠ 0) (t : ι → ℝ) :
    Summable fun i : ι =>
      (((z.im / Complex.normSq ((v i 0 : ℂ) * z + v i 1)) ^ s : ℝ) : ℂ) *
        Complex.exp (((-2 * Real.pi * E *
          (z.im / Complex.normSq ((v i 0 : ℂ) * z + v i 1)) : ℝ) : ℂ) +
          (t i : ℂ) * Complex.I) := by
  refine ((summable_poincare_height_comp z hs v hv).mul_left
    (Real.exp (2 * Real.pi * |E| * (z.im / EisensteinSeries.r z ^ 2)))).of_norm_bounded ?_
  intro i
  exact norm_poincare_seed_bound E s (t i)
    (div_nonneg z.im_pos.le (Complex.normSq_nonneg _))
    (poincare_height_le z (v i) (hne i))

/-- The Eisenstein majorant is summable on the actual cusp quotient. -/
theorem summable_cusp_height {s : ℝ} (hs : 1 < s) (z : UpperHalfPlane) :
    Summable fun q : CuspCoset => (q.out • z).im ^ s := by
  apply (summable_poincare_height_comp z hs cuspBottomRow cuspBottomRow_injective).congr
  intro q
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  rfl

/-- Every modular image has bounded height at a fixed point of the upper half-plane. -/
theorem cusp_height_le (z : UpperHalfPlane) (q : CuspCoset) :
    (q.out • z).im ≤ z.im / EisensteinSeries.r z ^ 2 := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  exact poincare_height_le z (cuspBottomRow q) (cuspBottomRow_ne_zero q)

/-- Absolute convergence of the actual coset Poincaré series for `s > 1`.
The energy is arbitrary real, including the negative vacuum seeds. -/
theorem summable_norm_poincareTerm (E : ℝ) (J : ℤ) {s : ℝ} (hs : 1 < s)
    (z : UpperHalfPlane) : Summable fun q : CuspCoset => ‖poincareTerm E J s z q‖ := by
  apply ((summable_cusp_height hs z).mul_left
    (Real.exp (2 * Real.pi * |E| * (z.im / EisensteinSeries.r z ^ 2)))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro q
  rw [poincareTerm_out]
  unfold pointSeed
  apply norm_poincare_seed_bound E s _ (q.out • z).im_pos.le
  exact cusp_height_le z q

theorem summable_poincareTerm (E : ℝ) (J : ℤ) {s : ℝ} (hs : 1 < s)
    (z : UpperHalfPlane) : Summable (poincareTerm E J s z) :=
  (summable_norm_poincareTerm E J hs z).of_norm

/-- An actual convergent-sum certificate for the series definition. -/
theorem hasSum_poincareTerm (E : ℝ) (J : ℤ) {s : ℝ} (hs : 1 < s)
    (z : UpperHalfPlane) : HasSum (poincareTerm E J s z) (poincareSeries E J s z) :=
  (summable_poincareTerm E J hs z).hasSum

/-- The direct point seed is exactly the identity-coset contribution. -/
theorem poincareSeries_direct_term (E : ℝ) (J : ℤ) {s : ℝ} (hs : 1 < s)
    (z : UpperHalfPlane) :
    poincareSeries E J s z = pointSeed E J s z +
      ∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, poincareTerm E J s z q := by
  classical
  have h := (summable_poincareTerm E J hs z).sum_add_tsum_compl
    (s := {identityCuspCoset})
  simp only [Finset.sum_singleton, poincareTerm_identity] at h
  let e : {q : CuspCoset // q ≠ identityCuspCoset} ≃
      ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ) :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  calc
    _ = pointSeed E J s z + ∑' q :
        ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ),
          poincareTerm E J s z q := h.symm
    _ = _ := congrArg (pointSeed E J s z + ·)
      (e.tsum_eq (fun q => poincareTerm E J s z q)).symm

/-- Subtracting the zero-energy seed exposes one extra power of height. -/
theorem pointSeed_sub_zero_energy (E : ℝ) (J : ℤ) (s : ℝ) (z : UpperHalfPlane) :
    pointSeed E J s z - pointSeed 0 J s z =
      (z.im ^ s : ℝ) * Complex.exp
        (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I) *
        (Complex.exp (((-2 * Real.pi * E * z.im : ℝ) : ℂ)) - 1) := by
  simp only [pointSeed, mul_zero, zero_mul, Complex.ofReal_zero, zero_add,
    Complex.exp_add]
  ring

/-- The gained-height estimate is uniform for bounded orbit heights and all real energies. -/
theorem norm_pointSeed_sub_zero_energy_le (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) {M : ℝ} (hzM : z.im ≤ M) :
    ‖pointSeed E J s z - pointSeed 0 J s z‖ ≤
      (2 * Real.pi * |E| * Real.exp (2 * Real.pi * |E| * M)) * z.im ^ (s + 1) := by
  rw [pointSeed_sub_zero_energy, norm_mul, norm_mul]
  have hphase : ‖Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hphase, mul_one, Complex.norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg z.im_pos.le _)]
  have hnorm : ‖(((-2 * Real.pi * E * z.im : ℝ) : ℂ))‖ =
      2 * Real.pi * |E| * z.im := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos z.im_pos]
  have hexp : ‖Complex.exp (((-2 * Real.pi * E * z.im : ℝ) : ℂ)) - 1‖ ≤
      (2 * Real.pi * |E| * z.im) * Real.exp (2 * Real.pi * |E| * z.im) := by
    simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_one, hnorm] using Complex.norm_exp_sub_sum_le_norm_mul_exp
      (((-2 * Real.pi * E * z.im : ℝ) : ℂ)) 1
  have hmono : Real.exp (2 * Real.pi * |E| * z.im) ≤
      Real.exp (2 * Real.pi * |E| * M) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzM (by positivity))
  calc
    _ ≤ z.im ^ s * ((2 * Real.pi * |E| * z.im) *
        Real.exp (2 * Real.pi * |E| * M)) :=
      mul_le_mul_of_nonneg_left
        (hexp.trans (mul_le_mul_of_nonneg_left hmono (by positivity)))
        (Real.rpow_nonneg z.im_pos.le _)
    _ = _ := by rw [Real.rpow_add_one z.im_pos.ne']; ring

/-- The zero-energy subtraction converges absolutely throughout the larger real
region `s > 0`, before any continuation of the zero-energy seed is supplied. -/
theorem summable_norm_poincareTerm_sub_zero (E : ℝ) (J : ℤ) {s : ℝ}
    (hs : 0 < s) (z : UpperHalfPlane) :
    Summable fun q : CuspCoset =>
      ‖poincareTerm E J s z q - poincareTerm 0 J s z q‖ := by
  apply ((summable_cusp_height (s := s + 1) (by linarith) z).mul_left
    (2 * Real.pi * |E| *
      Real.exp (2 * Real.pi * |E| * (z.im / EisensteinSeries.r z ^ 2)))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro q
  rw [poincareTerm_out, poincareTerm_out]
  exact norm_pointSeed_sub_zero_energy_le E J s (q.out • z) (cusp_height_le z q)

/-- The genuinely convergent energy correction, defined already for `s > 0`. -/
def poincareEnergyDifference (E : ℝ) (J : ℤ) (s : ℝ) (z : UpperHalfPlane) : ℂ :=
  ∑' q : CuspCoset, (poincareTerm E J s z q - poincareTerm 0 J s z q)

theorem hasSum_poincareEnergyDifference (E : ℝ) (J : ℤ) {s : ℝ}
    (hs : 0 < s) (z : UpperHalfPlane) :
    HasSum (fun q : CuspCoset => poincareTerm E J s z q - poincareTerm 0 J s z q)
      (poincareEnergyDifference E J s z) :=
  (summable_norm_poincareTerm_sub_zero E J hs z).of_norm.hasSum

/-- In the common convergence region the correction equals the difference of
the two original series, rather than a separately postulated function. -/
theorem poincareEnergyDifference_eq_sub (E : ℝ) (J : ℤ) {s : ℝ}
    (hs : 1 < s) (z : UpperHalfPlane) :
    poincareEnergyDifference E J s z =
      poincareSeries E J s z - poincareSeries 0 J s z :=
  (summable_poincareTerm E J hs z).tsum_sub (summable_poincareTerm 0 J hs z)

theorem poincareEnergyDifference_smul (E : ℝ) (J : ℤ) (s : ℝ)
    (z : UpperHalfPlane) (g : SL(2, ℤ)) :
    poincareEnergyDifference E J s (g • z) = poincareEnergyDifference E J s z := by
  simp only [poincareEnergyDifference, poincareTerm_smul]
  exact (cuspRightEquiv g).tsum_eq
    (fun q : CuspCoset => poincareTerm E J s z q - poincareTerm 0 J s z q)

end

end GapFamily.Analytic
