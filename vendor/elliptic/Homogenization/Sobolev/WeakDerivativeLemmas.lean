import Homogenization.Sobolev.WeakDerivatives

/-! Shared restriction and smooth-function lemmas for weak derivatives.
Both the H¹ and W¹ᵖ APIs use these same public declarations. -/

namespace Homogenization

theorem HasWeakPartialDerivOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := by
  let _ := hVopen
  intro φ hφ_smooth hφ_compact hφ_supp
  have hφ_suppU : tsupport φ ⊆ U := hφ_supp.trans hVU
  have key := h φ hφ_smooth hφ_compact hφ_suppU
  have h1 : ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_supp hx')
    have hφ_eq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have h2 : ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ_supp hx'))]
  have h3 : ∀ x, x ∉ U → u x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    fun x hx => h1 x (fun hx' => hx (hVU hx'))
  have h4 : ∀ x, x ∉ U → gi x * φ x = 0 :=
    fun x hx => h2 x (fun hx' => hx (hVU hx'))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h2,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h3,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h4,
    key]

theorem HasWeakGradientOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i
  exact (h i).restrict hVopen hVU

theorem HasWeakPartialDerivOn.of_contDiff {d : ℕ} {U : Set (Vec d)}
    {i : Fin d} {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDerivOn U i f (fun x => (fderiv ℝ f x) (basisVec i)) := by
  intro φ hφ_smooth hφ_supp hφ_sub
  let ei : Vec d := basisVec i
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
  have hf_cont : Continuous f := hf_diff.continuous
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hfderiv_φ_cont : Continuous (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using
      (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderiv_f_cont : Continuous (fun x => (fderiv ℝ f x) ei) := by
    simpa [ei] using
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ_fderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using hφ_supp.fderiv_apply (𝕜 := ℝ) ei
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simpa [ei] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        ((hfderiv_f_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
        ((hf_cont.mul hfderiv_φ_cont).integrable_of_hasCompactSupport hφ_fderiv_supp.mul_left)
        ((hf_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
        (fun x _ => hf_diff.differentiableAt) (fun x _ => hφ_diff.differentiableAt)
  ·
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    simp [image_eq_zero_of_notMem_tsupport hx_notin]
  ·
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    have hφ_eq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp

theorem HasWeakGradientOn.of_contDiff {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakGradientOn U f (fun x i => (fderiv ℝ f x) (basisVec i)) := by
  intro i
  exact HasWeakPartialDerivOn.of_contDiff hf

end Homogenization
