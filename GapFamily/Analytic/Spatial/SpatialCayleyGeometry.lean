import GapFamily.Analytic.Spatial.SpatialPointKernelBasic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set UpperHalfPlane

/-- The raw inverse Cayley map from the unit disk to the upper half-plane. -/
def cayleyToUpper (ζ : ℂ) : ℂ := Complex.I * (1 + ζ) / (1 - ζ)

theorem cayleyToUpper_den_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 - ζ ≠ 0 := by
  intro h
  have he : ζ = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hζ

theorem cayleyToUpper_normSq_lt_one {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    Complex.normSq ζ < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg ζ]

theorem cayleyToUpper_im (ζ : ℂ) :
    (cayleyToUpper ζ).im = (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  simp only [cayleyToUpper, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.sub_re, Complex.sub_im, zero_mul, one_mul, zero_add,
    zero_sub, Complex.normSq_apply]
  ring

theorem cayleyToUpper_im_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    0 < (cayleyToUpper ζ).im := by
  rw [cayleyToUpper_im]
  exact div_pos (sub_pos.mpr (cayleyToUpper_normSq_lt_one hζ))
    (Complex.normSq_pos.mpr (cayleyToUpper_den_ne_zero hζ))

theorem cayleyToUpper_add_I {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cayleyToUpper ζ + Complex.I = 2 * Complex.I / (1 - ζ) := by
  unfold cayleyToUpper
  field_simp [cayleyToUpper_den_ne_zero hζ]
  ring

theorem cayleyToUpper_hasDerivAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasDerivAt cayleyToUpper (2 * Complex.I / (1 - ζ) ^ 2) ζ := by
  have hn := ((hasDerivAt_id ζ).const_add 1).const_mul Complex.I
  have hd := (hasDerivAt_id ζ).const_sub 1
  unfold cayleyToUpper
  convert hn.fun_div hd (cayleyToUpper_den_ne_zero hζ) using 1 <;>
    simp only [id_eq, mul_one]
  ring

theorem cayleyToUpper_injOn_ball :
    InjOn cayleyToUpper (Metric.ball (0 : ℂ) 1) := by
  intro ζ hζ η hη h
  have hζ' : ‖ζ‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hζ
  have hη' : ‖η‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hη
  have hc := (div_eq_div_iff (cayleyToUpper_den_ne_zero hζ')
    (cayleyToUpper_den_ne_zero hη')).mp h
  have he : Complex.I * (2 * (ζ - η)) = 0 := by
    linear_combination hc
  have he' : 2 * (ζ - η) = 0 := (mul_eq_zero.mp he).resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_left (by norm_num))

theorem cayleyToUpper_image_ball :
    cayleyToUpper '' Metric.ball (0 : ℂ) 1 = upperHalfPlaneSet := by
  ext z
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    exact cayleyToUpper_im_pos (by simpa only [Metric.mem_ball, dist_zero_right] using hζ)
  · intro hz
    have hz' : 0 < z.im := hz
    have hp : z + Complex.I ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
      linarith
    let ζ : ℂ := (z - Complex.I) / (z + Complex.I)
    have hs : Complex.normSq ζ < 1 := by
      dsimp only [ζ]
      rw [Complex.normSq_div]
      apply (div_lt_one (Complex.normSq_pos.mpr hp)).mpr
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, sub_zero, add_zero]
      nlinarith
    have hζ : ‖ζ‖ < 1 := by
      rw [Complex.normSq_eq_norm_sq] at hs
      nlinarith [norm_nonneg ζ]
    refine ⟨ζ, by simpa only [Metric.mem_ball, dist_zero_right] using hζ, ?_⟩
    unfold cayleyToUpper
    apply (div_eq_iff (cayleyToUpper_den_ne_zero hζ)).mpr
    dsimp [ζ]
    field_simp [hp]
    ring

theorem pointParameter_cayleyToUpper_I {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    pointParameter (cayleyToUpper ζ) Complex.I = 1 / (1 - Complex.normSq ζ) := by
  have hn : Complex.normSq (1 - ζ) ≠ 0 :=
    (Complex.normSq_pos.mpr (cayleyToUpper_den_ne_zero hζ)).ne'
  have hq : 1 - Complex.normSq ζ ≠ 0 :=
    (sub_pos.mpr (cayleyToUpper_normSq_lt_one hζ)).ne'
  rw [pointParameter_eq_normSq_sub_conj (cayleyToUpper_im_pos hζ) (by norm_num)]
  simp only [Complex.conj_I, sub_neg_eq_add, Complex.I_im]
  rw [cayleyToUpper_add_I hζ, Complex.normSq_div, cayleyToUpper_im]
  norm_num [map_mul]
  field_simp [hn, hq]

end GapFamily.Analytic.SpatialPoint
