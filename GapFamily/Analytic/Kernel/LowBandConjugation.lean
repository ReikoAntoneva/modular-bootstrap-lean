import GapFamily.Analytic.Kernel.LowBandOperator

/-!
# Complex conjugation on the physical low band

The pointwise conjugation of each ordinary `L²` row gives an involutive
real-linear isometry of the finite Hilbert sum. Its representative and inner
product identities allow real kernel operators to preserve real data.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace GapFamily.Analytic

theorem lowBandRow_star_add {j : ℤ} {B : ℝ} (f g : LowBandRow j B) :
    star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g,
    Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g]
    with E hstar hadd hsum hf hg
  rw [hstar, hsum]
  simp only [Pi.star_apply, Pi.add_apply, hadd, hf, hg, star_add]

theorem lowBandRow_star_smul {j : ℤ} {B : ℝ} (c : ℂ) (f : LowBandRow j B) :
    star (c • f) = conj c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul (conj c) (star f), Lp.coeFn_star f] with E hstar hsmul htarget hf
  rw [hstar, htarget]
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, hsmul, hf, star_mul,
    Complex.star_def, mul_comm]

@[simp]
theorem norm_lowBandRow_star {j : ℤ} {B : ℝ} (f : LowBandRow j B) :
    ‖star f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  rw [eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

theorem inner_lowBandRow_star {j : ℤ} {B : ℝ} (f g : LowBandRow j B) :
    inner ℂ (star f) (star g) = conj (inner ℂ f g) := by
  rw [L2.inner_def, L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with E hf hg
  simp [hf, hg, RCLike.inner_apply]

/-- Componentwise complex conjugation of the finite physical Hilbert sum. -/
def lowBandConj {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert j B) : LowBandHilbert j B :=
  WithLp.toLp 2 (fun i => star (f i))

@[simp]
theorem lowBandConj_apply {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert j B) (i : ι) : lowBandConj j B f i = star (f i) := rfl

theorem lowBandConj_coeFn {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert j B) (i : ι) :
    ⇑(lowBandConj j B f i)
      =ᵐ[(referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B)]
        fun E => conj (f i E) := Lp.coeFn_star (f i)

@[simp]
theorem lowBandConj_involutive {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert j B) : lowBandConj j B (lowBandConj j B f) = f := by
  apply PiLp.ext
  intro i
  simp

@[simp]
theorem lowBandConj_add {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f g : LowBandHilbert j B) :
    lowBandConj j B (f + g) = lowBandConj j B f + lowBandConj j B g := by
  apply PiLp.ext
  intro i
  exact lowBandRow_star_add (f i) (g i)

@[simp]
theorem lowBandConj_smul {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (c : ℂ) (f : LowBandHilbert j B) :
    lowBandConj j B (c • f) = conj c • lowBandConj j B f := by
  apply PiLp.ext
  intro i
  exact lowBandRow_star_smul c (f i)

@[simp]
theorem norm_lowBandConj {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert j B) : ‖lowBandConj j B f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [PiLp.norm_sq_eq_of_L2, lowBandConj_apply, norm_lowBandRow_star]

theorem inner_lowBandConj {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f g : LowBandHilbert j B) :
    inner ℂ (lowBandConj j B f) (lowBandConj j B g) = conj (inner ℂ f g) := by
  simp only [PiLp.inner_apply, lowBandConj_apply, inner_lowBandRow_star, map_sum]

theorem inner_lowBandConj_right {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f g : LowBandHilbert j B) :
    inner ℂ f (lowBandConj j B g) = conj (inner ℂ (lowBandConj j B f) g) := by
  simpa using inner_lowBandConj j B (lowBandConj j B f) g

@[simp]
theorem lowBandConj_real_smul {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (c : ℝ) (f : LowBandHilbert j B) :
    lowBandConj j B (c • f) = c • lowBandConj j B f := by
  apply PiLp.ext
  intro i
  change star (c • f i) = c • star (f i)
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f i), Lp.coeFn_smul c (f i),
    Lp.coeFn_smul c (star (f i)), Lp.coeFn_star (f i)] with E hstar hsmul htarget hf
  rw [hstar, htarget]
  simp only [Pi.star_apply, Pi.smul_apply, hsmul, hf, star_smul, star_trivial]

/-- Complex conjugation as an involutive real-linear isometry equivalence. -/
def lowBandConjEquiv {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ) :
    LowBandHilbert j B ≃ₗᵢ[ℝ] LowBandHilbert j B where
  toFun := lowBandConj j B
  invFun := lowBandConj j B
  left_inv := lowBandConj_involutive j B
  right_inv := lowBandConj_involutive j B
  map_add' := lowBandConj_add j B
  map_smul' := lowBandConj_real_smul j B
  norm_map' := norm_lowBandConj j B

@[simp]
theorem lowBandConjEquiv_apply {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert j B) : lowBandConjEquiv j B f = lowBandConj j B f := rfl

@[simp]
theorem lowBandConjEquiv_symm_apply {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert j B) : (lowBandConjEquiv j B).symm f = lowBandConj j B f := rfl

end GapFamily.Analytic
