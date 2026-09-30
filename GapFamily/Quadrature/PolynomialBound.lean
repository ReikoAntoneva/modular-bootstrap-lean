import GapFamily.Quadrature.Variation
import GapFamily.Quadrature.UnitNodes
import GapFamily.Quadrature.MarkovBound
import GapFamily.Quadrature.PolynomialMass
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Topology.Algebra.Polynomial

/-!
# Bounds for nonnegative interval polynomials

The supremum-to-mass estimate comes from integrating beside a maximum over a
short interval where the derivative bound retains at least half the height.
-/

open Set MeasureTheory

namespace GapFamily.Quadrature

/-- A nonnegative Lipschitz peak has a definite amount of interval mass.
This geometric estimate will be applied with the proved polynomial derivative bound. -/
theorem peak_le_integral_of_lipschitz_bound
    {f : ℝ → ℝ} {a b t M R : ℝ} (hab : a < b) (hR : 1 ≤ R)
    (hf : ContinuousOn f (Icc a b)) (hfpos : ∀ x ∈ Icc a b, 0 ≤ f x)
    (ht : t ∈ Icc a b) (hM : f t = M)
    (hlip : ∀ x ∈ Icc a b, |f x - f t| ≤ (4 * R * M / (b-a)) * |x-t|) :
    M ≤ (16 * R / (b-a)) * ∫ x in a..b, f x := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hMpos : 0 ≤ M := hM ▸ hfpos t ht
  let δ := (b-a) / (8 * R)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ (b-a)/2 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 8*R)).mpr
    nlinarith
  have hL : 0 ≤ 4 * R * M / (b-a) := by positivity
  have hhalf (x : ℝ) (hx : x ∈ Icc a b) (hxt : |x-t| ≤ δ) : M/2 ≤ f x := by
    have hh := (hlip x hx).trans (mul_le_mul_of_nonneg_left hxt hL)
    have heq : (4 * R * M / (b-a)) * δ = M/2 := by
      dsimp [δ]
      field_simp
      ring
    rw [heq, hM] at hh
    have := (abs_le.mp hh).1
    linarith
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab.le
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] f := by
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun x hx => hfpos x (Ioc_subset_Icc_self hx))
  have hsmall (c d : ℝ) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
      (hlen : d-c = δ) (hnear : ∀ x ∈ Icc c d, |x-t| ≤ δ) :
      δ * M / 2 ≤ ∫ x in a..b, f x := by
    have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
    have hlocal : (∫ x in c..d, M/2) ≤ ∫ x in c..d, f x :=
      intervalIntegral.integral_mono_on hcd (intervalIntegrable_const)
        ((hf.mono hsub).intervalIntegrable_of_Icc hcd)
        (fun x hx => hhalf x (hsub hx) (hnear x hx))
    have hlarge := intervalIntegral.integral_mono_interval hac hcd hdb hnonneg hfi
    calc δ * M / 2 = ∫ x in c..d, M/2 := by simp [hlen]
         _ ≤ _ := hlocal.trans hlarge
  have hmass : δ * M / 2 ≤ ∫ x in a..b, f x := by
    rcases le_total t ((a+b)/2) with htleft | htright
    · apply hsmall t (t+δ) ht.1 (by linarith) (by linarith) (by ring)
      intro x hx
      rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x-t)]
      linarith [hx.2]
    · apply hsmall (t-δ) t (by linarith) (by linarith) ht.2 (by ring)
      intro x hx
      rw [abs_of_nonpos (by linarith [hx.2] : x-t ≤ 0)]
      linarith [hx.1]
  have hmul := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 16*R/(b-a) by positivity)
  have heq : (16*R/(b-a)) * (δ*M/2) = M := by
    dsimp [δ]
    field_simp
    ring
  rwa [heq] at hmul

/-- A nonzero polynomial which is nonnegative on a nondegenerate interval has
strictly positive ordinary integral on that interval. -/
theorem polynomial_integral_pos_of_nonnegative
    (p : Polynomial ℝ) {a b : ℝ} (hab : a < b) (hp : p ≠ 0)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) : 0 < ∫ x in a..b, p.eval x := by
  have hex : ∃ x ∈ Icc a b, p.eval x ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply p.eq_zero_of_infinite_isRoot
    exact (Icc_infinite hab).mono (fun x hx => h x hx)
  obtain ⟨x, hx, hpx⟩ := hex
  apply intervalIntegral.integral_pos hab p.continuous.continuousOn
    (fun y hy => hpos y (Ioc_subset_Icc_self hy))
  exact ⟨x, hx, lt_of_le_of_ne (hpos x hx) hpx.symm⟩

/-- The actual polynomial functional associated to any integrable signed density.
Polynomial evaluation is bounded on the compact interval, so every integral exists. -/
noncomputable def signedDensityFunctional (a b : ℝ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in a..b, p.eval x * f x
  map_add' p q := by
    simp only [Polynomial.eval_add, add_mul]
    exact intervalIntegral.integral_add (hf.continuousOn_mul p.continuous.continuousOn)
      (hf.continuousOn_mul q.continuous.continuousOn)
  map_smul' c p := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul c _

/-- A nonnegative polynomial cannot have an arbitrarily narrow peak: its
height is bounded by its ordinary integral with the explicit C3 degree loss. -/
theorem polynomial_eval_le_integral
    (p : Polynomial ℝ) (k : ℕ) {a b : ℝ} (hab : a < b) (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) {x : ℝ} (hx : x ∈ Icc a b) :
    p.eval x ≤ (16 * ((k : ℝ)+1)^3 / (b-a)) * ∫ y in a..b, p.eval y := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab.le) p.continuous.continuousOn
  have hbnd (y : ℝ) (hy : y ∈ Icc a b) : |p.eval y| ≤ p.eval t := by
    rw [abs_of_nonneg (hpos y hy)]
    exact hmax hy
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hr : 1 ≤ (k : ℝ)+1 := by linarith
  refine (hmax hx).trans (peak_le_integral_of_lipschitz_bound hab (one_le_pow₀ hr)
    p.continuous.continuousOn hpos ht rfl ?_)
  intro y hy
  have hdbound : ∀ z ∈ Icc a b, ‖deriv p.eval z‖ ≤
      4 * ((k : ℝ)+1)^3 * p.eval t / (b-a) := by
    intro z hz
    simpa only [p.deriv, Real.norm_eq_abs] using
      polynomial_derivative_abs_le_degree_succ_cube p k hab hdeg hbnd hz
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Icc a b) => p.differentiable.differentiableAt)
    hdbound (convex_Icc a b) ht hy

/-- The default C3 lower bound on the second spatial moment, including intervals
whose left endpoint is zero. -/
theorem polynomial_sq_mul_integral_lower
    (p : Polynomial ℝ) (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hdeg : p.natDegree ≤ k) (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) :
    (b-a)^2 / (8192 * ((k : ℝ)+1)^6) * (∫ x in a..b, p.eval x) ≤
      ∫ x in a..b, x^2 * p.eval x := by
  apply sq_mul_integral_lower_of_sup_bound ha hab (by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith)
    p.continuous.continuousOn hpos
  intro x hx
  exact polynomial_eval_le_integral p k hab hdeg hpos hx

/-- Partition variation satisfies the exact polynomial loss used in C3. -/
theorem polynomial_variation_le_integral
    (p : Polynomial ℝ) (k : ℕ) {a b : ℝ} (hab : a < b) (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) :
    (eVariationOn p.eval (Icc a b)).toReal ≤
      (64 * ((k : ℝ)+1)^6 / (b-a)) * ∫ x in a..b, p.eval x := by
  let M := (16 * ((k : ℝ)+1)^3 / (b-a)) * ∫ x in a..b, p.eval x
  have hbnd (x : ℝ) (hx : x ∈ Icc a b) : |p.eval x| ≤ M := by
    rw [abs_of_nonneg (hpos x hx)]
    exact polynomial_eval_le_integral p k hab hdeg hpos hx
  calc
    _ ≤ ∫ x in a..b, |p.derivative.eval x| :=
      polynomial_variation_le_integral_abs_derivative p hab.le
    _ ≤ ∫ x in a..b, 4 * ((k : ℝ)+1)^3 * M / (b-a) :=
      intervalIntegral.integral_mono_on hab.le
        (p.derivative.continuous.abs.intervalIntegrable a b) intervalIntegrable_const
        (fun x hx => polynomial_derivative_abs_le_degree_succ_cube p k hab hdeg hbnd hx)
    _ = _ := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      dsimp [M]
      field_simp
      ring

/-- A quadratic lower bound on an ordinary signed density gives the C3 lower
bound on every nonnegative polynomial functional value. -/
theorem signedDensityFunctional_lower
    {a b A B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ x ∈ Icc a b, A*x^2-B ≤ f x)
    (p : Polynomial ℝ) (k : ℕ) (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) :
    (A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B) * (∫ x in a..b, p.eval x) ≤
      signedDensityFunctional a b f hf p := by
  have hpint : IntervalIntegrable p.eval volume a b := p.continuous.intervalIntegrable a b
  have hsqint : IntervalIntegrable (fun x : ℝ => x^2*p.eval x) volume a b :=
    ((continuous_id.pow 2).mul p.continuous).intervalIntegrable a b
  have hmono : (∫ x in a..b, p.eval x * (A*x^2-B)) ≤
      signedDensityFunctional a b f hf p := by
    apply intervalIntegral.integral_mono_on hab.le
      ((p.continuous.mul ((continuous_const.mul (continuous_id.pow 2)).sub
        continuous_const)).intervalIntegrable a b)
      (hf.continuousOn_mul p.continuous.continuousOn)
    intro x hx
    exact mul_le_mul_of_nonneg_left (hbound x hx) (hpos x hx)
  have heq : (∫ x in a..b, p.eval x * (A*x^2-B)) =
      A*(∫ x in a..b, x^2*p.eval x)-B*(∫ x in a..b, p.eval x) := by
    calc
      _ = ∫ x in a..b, A*(x^2*p.eval x)-B*p.eval x := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hsqint.const_mul A) (hpint.const_mul B),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [heq] at hmono
  have hsq := mul_le_mul_of_nonneg_left
    (polynomial_sq_mul_integral_lower p k ha hab hdeg hpos) hA
  apply le_trans _ hmono
  calc
    _ = A*((b-a)^2/(8192*((k : ℝ)+1)^6)*(∫ x in a..b, p.eval x))-
        B*(∫ x in a..b, p.eval x) := by ring
    _ ≤ _ := sub_le_sub_right hsq _

/-- A positive C3 bracket gives strict positivity on all nonzero nonnegative
polynomials of the requested degree, even when the density itself changes sign. -/
theorem signedDensityFunctional_strictPositive
    {a b A B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ x ∈ Icc a b, A*x^2-B ≤ f x)
    (k : ℕ) (hbracket : 0 < A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ k) (hp : p ≠ 0)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) :
    0 < signedDensityFunctional a b f hf p :=
  (mul_pos hbracket (polynomial_integral_pos_of_nonnegative p hab hp hpos)).trans_le
    (signedDensityFunctional_lower ha hab hA f hf hbound p k hdeg hpos)

/-- The C3 lower bound supplies the actual partition-variation reserve. -/
theorem signedDensityFunctional_variation_reserve
    {a b A B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ x ∈ Icc a b, A*x^2-B ≤ f x)
    (k : ℕ) (hbracket : 0 ≤ A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) :
    ((A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)*(b-a)/(64*((k : ℝ)+1)^6)) *
        (eVariationOn p.eval (Icc a b)).toReal ≤ signedDensityFunctional a b f hf p := by
  have hδ : 0 ≤ (A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)*(b-a)/(64*((k : ℝ)+1)^6) :=
    div_nonneg (mul_nonneg hbracket (sub_nonneg.mpr hab.le)) (by positivity)
  have hvar := mul_le_mul_of_nonneg_left
    (polynomial_variation_le_integral p k hab hdeg hpos) hδ
  apply hvar.trans
  have heq : ((A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)*(b-a)/(64*((k : ℝ)+1)^6)) *
      ((64*((k : ℝ)+1)^6/(b-a))*(∫ x in a..b, p.eval x)) =
      (A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)*(∫ x in a..b, p.eval x) := by
    have hd : b-a ≠ 0 := sub_ne_zero.mpr hab.ne'
    have hr : (k : ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [heq]
  exact signedDensityFunctional_lower ha hab hA f hf hbound p k hdeg hpos

/-- C3 followed by C4: an integrable signed density with the stated quadratic
lower bound and numerical reserve is represented, through degree `k`, by exactly
its prescribed positive integer mass in unit nodes. -/
theorem exists_unit_nodes_of_signed_density_lower_bound
    {a b A B : ℝ} {k N : ℕ} (ha : 0 ≤ a) (hab : a < b) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ x ∈ Icc a b, A*x^2-B ≤ f x) (hN : 0 < N)
    (hmass : (∫ x in a..b, f x) = (N : ℝ))
    (hreserve : 1/2 <
      (A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)*(b-a)/(64*((k : ℝ)+1)^6)) :
    ∃ node : Fin N → ℝ, (∀ j, node j ∈ Icc a b) ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ k →
        ∑ j, p.eval (node j) = ∫ x in a..b, p.eval x * f x := by
  have hbracket : 0 ≤ A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B := by
    have hp : 0 < (A*(b-a)^2/(8192*((k : ℝ)+1)^6)-B)*(b-a)/(64*((k : ℝ)+1)^6) :=
      lt_trans (by norm_num) hreserve
    have hd : 0 < 64*((k : ℝ)+1)^6 := by positivity
    have hm := (div_pos_iff_of_pos_right hd).mp hp
    exact (pos_of_mul_pos_left hm (sub_nonneg.mpr hab.le)).le
  apply exists_unit_nodes_of_variation_reserve hab hN hreserve
    (signedDensityFunctional a b f hf)
  · simpa [signedDensityFunctional] using hmass
  · intro p hp hpos
    exact signedDensityFunctional_variation_reserve ha hab hA f hf hbound k hbracket p hp hpos

end GapFamily.Quadrature
