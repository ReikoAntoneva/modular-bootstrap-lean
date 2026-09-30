import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Ordinary negative-density integral

The negative mass of a real density is bounded by the ordinary absolute integral
of its error from a nonnegative density. If the density is nonnegative outside a
measurable set, only the error on that set needs to be integrable. The ambient
measure need not be finite.
-/

open MeasureTheory Set

namespace GapFamily.Analytic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {q L err : α → ℝ} {s : Set α}

/-- The pointwise negative part is controlled by the error from a nonnegative
leading term. No size bound on the leading term is needed. -/
theorem negPart_le_abs_error {q L err : ℝ} (hdecomp : q = L + err)
    (hL : 0 ≤ L) : max (-q) 0 ≤ |err| := by
  apply max_le
  · have he := neg_abs_le err
    linarith
  · exact abs_nonneg err

/-- Ordinary negative mass is bounded by the absolute integral of the error
from a nonnegative leading term, even for an infinite ambient measure. -/
theorem integral_negPart_le_integral_abs_of_nonneg
    (hq : Integrable q μ) (herr : Integrable err μ)
    (hdecomp : ∀ᵐ x ∂μ, q x = L x + err x)
    (hL : ∀ᵐ x ∂μ, 0 ≤ L x) :
    (∫ x, max (-q x) 0 ∂μ) ≤ ∫ x, |err x| ∂μ := by
  apply integral_mono_ae hq.neg_part herr.abs
  filter_upwards [hdecomp, hL] with x hx hLx
  exact negPart_le_abs_error hx hLx

/-- A real density nonnegative off a measurable set has all its negative mass
on that set. This identity does not need an integrability hypothesis. -/
theorem integral_negPart_eq_setIntegral (hs : MeasurableSet s)
    (houtside : ∀ᵐ x ∂μ.restrict sᶜ, 0 ≤ q x) :
    (∫ x, max (-q x) 0 ∂μ) = ∫ x in s, max (-q x) 0 ∂μ := by
  have hz : (fun x => max (-q x) 0) =ᵐ[μ.restrict sᶜ] 0 := by
    filter_upwards [houtside] with x hx
    exact max_eq_right (neg_nonpos.mpr hx)
  rw [← integral_indicator hs]
  exact (integral_congr_ae
    (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hz)).symm

/-- A version of localization with the nonnegativity hypothesis expressed as
an almost-everywhere implication for the ambient measure. -/
theorem integral_negPart_eq_setIntegral_of_ae (hs : MeasurableSet s)
    (houtside : ∀ᵐ x ∂μ, x ∉ s → 0 ≤ q x) :
    (∫ x, max (-q x) 0 ∂μ) = ∫ x in s, max (-q x) 0 ∂μ := by
  apply integral_negPart_eq_setIntegral hs
  exact (ae_restrict_iff' hs.compl).2 houtside

/-- Local integrability on the region where negativity can occur suffices for
global integrability of the negative part. The positive density may grow outside
that region and need not be globally integrable. -/
theorem integrable_negPart_of_local (hs : MeasurableSet s)
    (hq : IntegrableOn q s μ)
    (houtside : ∀ᵐ x ∂μ.restrict sᶜ, 0 ≤ q x) :
    Integrable (fun x => max (-q x) 0) μ := by
  have hz : (fun x => max (-q x) 0) =ᵐ[μ.restrict sᶜ] 0 := by
    filter_upwards [houtside] with x hx
    exact max_eq_right (neg_nonpos.mpr hx)
  have hn : IntegrableOn (fun x => max (-q x) 0) s μ := hq.neg_part
  exact (hn.integrable_indicator hs).congr
    (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hz)

/-- A density whose negative part is confined to `s` only needs integrability
of the density and error on `s` for its global negative-mass bound. -/
theorem integral_negPart_le_setIntegral_abs
    (hs : MeasurableSet s) (hq : IntegrableOn q s μ)
    (herr : IntegrableOn err s μ)
    (hdecomp : ∀ᵐ x ∂μ.restrict s, q x = L x + err x)
    (hL : ∀ᵐ x ∂μ.restrict s, 0 ≤ L x)
    (houtside : ∀ᵐ x ∂μ.restrict sᶜ, 0 ≤ q x) :
    (∫ x, max (-q x) 0 ∂μ) ≤ ∫ x in s, |err x| ∂μ := by
  rw [integral_negPart_eq_setIntegral hs houtside]
  exact integral_negPart_le_integral_abs_of_nonneg hq herr hdecomp hL

end GapFamily.Analytic
