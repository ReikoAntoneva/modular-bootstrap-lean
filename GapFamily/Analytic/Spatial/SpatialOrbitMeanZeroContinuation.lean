import GapFamily.Analytic.Spatial.SpatialOrbitMeanZero
import GapFamily.Analytic.Modular.ModularMeanZeroResolventCommute
import GapFamily.Analytic.Foundation.CommutingRecurrenceLimit

/-! The positive mean-zero resolvent branch reaches the open interval above
one half. Its identity with the literal orbit kernel in the original
convergence half-plane is proved below. The endpoint at one half requires
a separate limiting argument and is not defined by the totalized inverse. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Filter ModularGradient ModularPositiveResolvent
open ModularMeanZeroResolvent
open scoped Topology ComplexOrder

/-- Every actual mean-zero resolvent commutes with the normalized orbit
operator. The proof uses the actual operator recurrence and its strong tail
limit, rather than assuming a spectral functional calculus. -/
theorem meanZeroResolvent_normalizedOrbitOperator_commute
    (a s : ℝ) (hs : 1 < s) :
    Commute (meanZeroResolvent a) (normalizedOrbitOperator s hs) := by
  let q : ℕ → ℝ := fun n => s + (n : ℝ)
  have hq (n : ℕ) : 1 < q n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [q]
    linarith
  have hqLim : Tendsto q atTop atTop := by
    simpa only [q, add_comm] using
      (tendsto_atTop_add_const_right atTop s tendsto_natCast_atTop_atTop)
  let r : ℕ → ℝ := fun n => q n * (q n - 1)
  have hr (n : ℕ) : 0 < r n :=
    mul_pos (lt_trans zero_lt_one (hq n)) (sub_pos.mpr (hq n))
  have hrec (n : ℕ) : normalizedOrbitOperator (q n) (hq n) =
      resolventFactor (r n) * normalizedOrbitOperator (q (n + 1)) (hq (n + 1)) := by
    simpa only [q, r, Nat.cast_add, Nat.cast_one, add_assoc] using
      normalizedOrbitOperator_resolvent_recurrence (q n) (hq n)
  have h := CommutingRecurrenceLimit.commute_of_contraction_recurrence
    (fun n => normalizedOrbitOperator (q n) (hq n))
    (fun n => resolventFactor (r n)) (meanZeroResolvent a)
    (fun n => meanZeroResolvent_resolventFactor_commute a (r n))
    (fun n => resolventFactor_norm_le_one (r n) (hr n)) hrec
    (normalizedOrbitOperator_tendsto q hq hqLim)
  simpa only [q, Nat.cast_zero, add_zero] using h

/-- Removing the mass normalization preserves the actual commutation. -/
theorem meanZeroResolvent_spatialOrbitIntegralOperator_commute
    (a s : ℝ) (hs : 1 < s) :
    Commute (meanZeroResolvent a) (spatialOrbitIntegralOperator s hs) := by
  have h := (meanZeroResolvent_normalizedOrbitOperator_commute a s hs).smul_right
    (((Real.pi / (s - 1) : ℝ)) : ℂ)
  have he : (((Real.pi / (s - 1) : ℝ)) : ℂ) • normalizedOrbitOperator s hs =
      spatialOrbitIntegralOperator s hs := by
    rw [normalizedOrbitOperator, smul_smul]
    have hc : (((Real.pi / (s - 1) : ℝ)) : ℂ) * ((((s - 1) / Real.pi : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      have hreal : Real.pi / (s - 1) * ((s - 1) / Real.pi) = 1 := by
        field_simp [Real.pi_ne_zero, sub_ne_zero.mpr hs.ne']
      rw [hreal, Complex.ofReal_one]
    rw [hc, one_smul]
  rwa [he] at h

/-- The genuine shifted recurrence, with the actual mean-zero resolvent and
the convergent spatial operator at the shifted exponent. The parameter one
is allowed because its constant mode has already been removed. -/
def spatialOrbitMeanZeroContinuation (s : ℝ) (hs : 1 / 2 < s) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  (s : ℂ) ^ 2 • ((meanZeroResolvent (s * (1 - s))) *
    spatialOrbitIntegralOperator (s + 1) (by linarith))

/-- The quarter gap applies strictly above the target threshold. -/
theorem spatialOrbit_shift_lt_quarter (s : ℝ) (hs : 1 / 2 < s) :
    s * (1 - s) < 1 / 4 := by
  nlinarith [sq_pos_of_pos (show 0 < s - 1 / 2 by linarith)]

/-- Positivity is proved for the actual recurrence branch all the way down
to, but excluding, one half. No positivity input appears in the theorem. -/
theorem spatialOrbitMeanZeroContinuation_isPositive (s : ℝ) (hs : 1 / 2 < s) :
    (spatialOrbitMeanZeroContinuation s hs).IsPositive := by
  have hp := PositiveContractionProduct.isPositive_mul_of_commute
      (meanZeroResolvent_isPositive (s * (1 - s)) (spatialOrbit_shift_lt_quarter s hs))
      (spatialOrbitIntegralOperator_isPositive (s + 1) (by linarith))
      (meanZeroResolvent_spatialOrbitIntegralOperator_commute
        (s * (1 - s)) (s + 1) (by linarith))
  apply hp.smul_of_nonneg
  exact_mod_cast sq_nonneg s

/-- The continued branch still takes values in the genuine mean-zero
subspace, including between the convergence line and the threshold. -/
theorem spatialOrbitMeanZeroContinuation_mem_meanZero
    (s : ℝ) (hs : 1 / 2 < s) (f : ModularHilbert) :
    spatialOrbitMeanZeroContinuation s hs f ∈ modularMeanZero := by
  change (s : ℂ) ^ 2 • meanZeroResolvent (s * (1 - s))
    (spatialOrbitIntegralOperator (s + 1) (by linarith) f) ∈ modularMeanZero
  exact modularMeanZero.smul_mem _ (meanZeroResolvent_mem_meanZero _ _)

/-- Every value before the threshold remains in the actual unbounded
Laplacian domain. This is not a statement about the endpoint. -/
theorem spatialOrbitMeanZeroContinuation_mem_laplacian_domain
    (s : ℝ) (hs : 1 / 2 < s) (f : ModularHilbert) :
    spatialOrbitMeanZeroContinuation s hs f ∈ laplacian.domain := by
  change (s : ℂ) ^ 2 • meanZeroResolvent (s * (1 - s))
    (spatialOrbitIntegralOperator (s + 1) (by linarith) f) ∈ laplacian.domain
  exact laplacian.domain.smul_mem _ (meanZeroResolvent_mem_domain _ _)

/-- In the common half-plane the recurrence branch is exactly the
orthogonal compression of the literal spatial orbit integral operator. -/
theorem spatialOrbitMeanZeroContinuation_eq_meanZeroOperator (s : ℝ) (hs : 1 < s) :
    spatialOrbitMeanZeroContinuation s (by linarith) = spatialOrbitMeanZeroOperator s hs := by
  apply ContinuousLinearMap.ext
  intro f
  have hshift := laplacian_spatialOrbitIntegralOperator s hs f
  have hleft := meanZeroResolvent_leftInverse (s * (1 - s))
    (spatialOrbit_shift_lt_quarter s (by linarith))
    ⟨spatialOrbitIntegralOperator s hs f,
      spatialOrbitIntegralOperator_mem_laplacian_domain s hs f⟩
  have hcast : ((s * (1 - s) : ℝ) : ℂ) = (s : ℂ) * (1 - (s : ℂ)) := by push_cast; rfl
  rw [hshift, hcast, add_sub_cancel_left, map_smul] at hleft
  change (s : ℂ) ^ 2 • meanZeroResolvent (s * (1 - s))
    (spatialOrbitIntegralOperator (s + 1) (by linarith) f) = _
  rw [hleft, spatialOrbitMeanZeroOperator_eq_sub]
  rw [modularMeanZeroProjection_eq]
  change spatialOrbitIntegralOperator s hs f - modularConstantProjection
    (spatialOrbitIntegralOperator s hs f) =
      spatialOrbitIntegralOperator s hs f -
        (((Real.pi / (s - 1) : ℝ)) : ℂ) • modularConstantProjection f
  have h := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (constantProjection_comp_spatialOrbitIntegralOperator s hs)
  exact congrArg (fun x => spatialOrbitIntegralOperator s hs f - x) h

/-- In the original convergence region, the continued branch has precisely
the literal kernel with its constant spectral term removed. -/
theorem spatialOrbitMeanZeroContinuation_ae (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) :
    spatialOrbitMeanZeroContinuation s (by linarith) f =ᵐ[modularMeasure]
      fun z => ∫ w, spatialOrbitMeanZeroKernel s z w * f w ∂modularMeasure := by
  rw [spatialOrbitMeanZeroContinuation_eq_meanZeroOperator s hs]
  exact spatialOrbitMeanZeroOperator_ae s hs f

end GapFamily.Analytic.SpatialPoint
