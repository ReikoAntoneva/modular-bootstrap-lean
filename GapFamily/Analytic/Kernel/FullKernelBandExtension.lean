import GapFamily.Analytic.Kernel.LowBandExtension
import GapFamily.Analytic.Kernel.FullKernelSmoothing

/-!
# The corrected operator on nested physical bands

The actual larger-band operator applied to a zero-extended input is represented
by the original input's ordinary kernel response throughout the larger output
band. The compressed kernel and identity-plus-kernel inner products agree
exactly with the smaller-band ones.
-/

noncomputable section

open MeasureTheory

namespace GapFamily.Analytic

theorem correctedKernelRowResponse_extension_eq (j J : ℤ) {b B : ℝ}
    (hbB : b ≤ B) (f : LowBandRow J b) (e : ℝ) :
    correctedKernelRowResponse j J B (lowBandRowExtension J hbB f) e =
      correctedKernelRowResponse j J b f e :=
  integral_mul_lowBandRowExtension_eq J hbB (correctedKernel j J e) f

theorem correctedKernelResponse_extension_eq {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B) (f : LowBandHilbert J b)
    (j : ℤ) (e : ℝ) :
    correctedKernelResponse J B (lowBandHilbertExtension J hbB f) j e =
      correctedKernelResponse J b f j e := by
  simp only [correctedKernelResponse, lowBandHilbertExtension_apply,
    correctedKernelRowResponse_extension_eq]

/-- The larger-band Riesz operator is represented throughout that band by
the ordinary response to the input on its original smaller band. -/
theorem correctedLowBandOperator_extension_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B) (hB : 0 ≤ B)
    (f : LowBandHilbert J b) (i : ι) :
    ⇑(correctedLowBandOperator J B (lowBandHilbertExtension J hbB f) i)
      =ᵐ[(referenceMeasure (J i)).restrict (Set.Ioo |(J i : ℝ)| B)]
        fun e => correctedKernelResponse J b f (J i) e := by
  filter_upwards [correctedLowBandOperator_coeFn J B hB
    (lowBandHilbertExtension J hbB f) i] with e he
  exact he.trans (correctedKernelResponse_extension_eq J hbB f (J i) e)

/-- The larger-band identity-plus-kernel image has its original input only
on the smaller band and its response throughout the larger band. -/
theorem correctedLowBandIdentityPlus_extension_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B) (hB : 0 ≤ B)
    (f : LowBandHilbert J b) (i : ι) :
    ⇑(correctedLowBandIdentityPlus J B (lowBandHilbertExtension J hbB f) i)
      =ᵐ[(referenceMeasure (J i)).restrict (Set.Ioo |(J i : ℝ)| B)]
        fun e => (Set.Ioo |(J i : ℝ)| b).indicator (⇑(f i)) e +
          correctedKernelResponse J b f (J i) e := by
  simp only [correctedLowBandIdentityPlus_apply, PiLp.add_apply]
  filter_upwards [Lp.coeFn_add (lowBandHilbertExtension J hbB f i)
    (correctedLowBandOperator J B (lowBandHilbertExtension J hbB f) i),
    lowBandHilbertExtension_coeFn J hbB f i,
    correctedLowBandOperator_extension_coeFn J hbB hB f i] with e hadd hext hresponse
  exact hadd.trans (congrArg₂ (· + ·) hext hresponse)

/-- On the exterior part of the larger band, the image is exactly the
ordinary response. This identifies the observable used by propagation. -/
theorem correctedLowBandIdentityPlus_extension_coeFn_exterior {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B) (hB : 0 ≤ B)
    (f : LowBandHilbert J b) (i : ι) :
    ∀ᵐ e ∂(referenceMeasure (J i)).restrict (Set.Ioo |(J i : ℝ)| B),
      b ≤ e → correctedLowBandIdentityPlus J B (lowBandHilbertExtension J hbB f) i e =
        correctedKernelResponse J b f (J i) e := by
  filter_upwards [correctedLowBandIdentityPlus_extension_coeFn J hbB hB f i] with e he heb
  have hnot : e ∉ Set.Ioo |(J i : ℝ)| b := fun h => (not_lt_of_ge heb) h.2
  simpa only [Set.indicator_of_notMem hnot, zero_add] using he

theorem inner_correctedLowBandOperator_extension {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B) (f g : LowBandHilbert J b) :
    inner ℂ (lowBandHilbertExtension J hbB f)
      (correctedLowBandOperator J B (lowBandHilbertExtension J hbB g)) =
      inner ℂ f (correctedLowBandOperator J b g) := by
  rw [inner_correctedLowBandOperator, inner_correctedLowBandOperator]
  exact lowBandHilbertForm_extension_eq J hbB
    (fun i l p => correctedKernel (J i) (J l) p.1 p.2) f g

/-- Exact compression of the actual identity-plus-kernel operator. -/
theorem inner_correctedLowBandIdentityPlus_extension {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B) (f g : LowBandHilbert J b) :
    inner ℂ (lowBandHilbertExtension J hbB f)
      (correctedLowBandIdentityPlus J B (lowBandHilbertExtension J hbB g)) =
      inner ℂ f (correctedLowBandIdentityPlus J b g) := by
  simp only [correctedLowBandIdentityPlus_apply, inner_add_right,
    (lowBandHilbertExtension J hbB).inner_map_map,
    inner_correctedLowBandOperator_extension]

end GapFamily.Analytic
