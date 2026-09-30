import BTZEntropy.Analytic.PartitionSeries
import BTZEntropy.Analytic.DescendantEta

/-!
# Complete descendant thermal expansion

The actual partition coefficients, the convergent Euler product, and the eta
characters now agree. In particular the sum over the same full-state labels
used by `smoothCount` converges to the existing torus partition function at
zero angular potential. Every convergence hypothesis is discharged here.
-/

noncomputable section

namespace BTZEntropy

/-- The actual Boltzmann descendant series sums to the convergent Euler product. -/
theorem hasSum_partitionThermalTerm {β : ℝ} (hβ : 0 < β) :
    HasSum (partitionThermalTerm β) (descendantEuler β) := by
  have h := hasSum_partitionCount_mul_pow (thermalNome_pos β).le
    (thermalNome_lt_one hβ)
  convert h using 1
  · funext n
    unfold partitionThermalTerm thermalNome
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  · rfl

theorem summable_partitionThermalTerm {β : ℝ} (hβ : 0 < β) :
    Summable (partitionThermalTerm β) := (hasSum_partitionThermalTerm hβ).summable

theorem partitionThermal_eq_descendantEuler {β : ℝ} (hβ : 0 < β) :
    partitionThermal β = descendantEuler β := (hasSum_partitionThermalTerm hβ).tsum_eq

theorem partitionThermal_pos {β : ℝ} (hβ : 0 < β) : 0 < partitionThermal β := by
  rw [partitionThermal_eq_descendantEuler hβ]
  exact descendantEuler_pos hβ

theorem summable_vacuumThermalTerm {β : ℝ} (hβ : 0 < β) :
    Summable (vacuumThermalTerm β) :=
  summable_vacuumThermalTerm_of_partition (summable_partitionThermalTerm hβ)

/-- The exact chiral vacuum null subtraction, with actual series convergence. -/
theorem vacuumThermal_eq {β : ℝ} (hβ : 0 < β) :
    vacuumThermal β = (1 - Real.exp (-β)) * partitionThermal β :=
  vacuumThermal_eq_of_summable (summable_partitionThermalTerm hβ)

theorem hasSum_vacuumThermalTerm {β : ℝ} (hβ : 0 < β) :
    HasSum (vacuumThermalTerm β) ((1 - Real.exp (-β)) * descendantEuler β) := by
  convert (summable_vacuumThermalTerm hβ).hasSum using 1
  rw [show (∑' n, vacuumThermalTerm β n) = vacuumThermal β from rfl,
    vacuumThermal_eq hβ, partitionThermal_eq_descendantEuler hβ]

/-- Absolute thermal convergence of every full descendant module and primary
copy follows from the already required primary thermal convergence. -/
theorem hasSum_stateThermalTerm {c β : ℝ} {s : GapFamily.Spectrum}
    (hs : GapFamily.TorusAdmissible c s) (hβ : 0 < β) :
    HasSum (stateThermalTerm β c s)
      (Real.exp (β * c / 12) *
        (vacuumThermal β ^ 2 + primaryThermal β s * partitionThermal β ^ 2)) :=
  hasSum_stateThermalTerm_of_partition hs hβ (summable_partitionThermalTerm hβ)

theorem summable_stateThermalTerm {c β : ℝ} {s : GapFamily.Spectrum}
    (hs : GapFamily.TorusAdmissible c s) (hβ : 0 < β) :
    Summable (stateThermalTerm β c s) := (hasSum_stateThermalTerm hs hβ).summable

/-- The full-state thermal sum is the literal existing character partition function. -/
theorem stateThermal_eq_partitionFunction {c β : ℝ} {s : GapFamily.Spectrum}
    (hs : GapFamily.TorusAdmissible c s) (hβ : 0 < β) :
    (stateThermal β c s : ℂ) =
      GapFamily.partitionFunction c s (thermalPoint β hβ) := by
  unfold stateThermal
  rw [(hasSum_stateThermalTerm hs hβ).tsum_eq,
    vacuumThermal_eq hβ, partitionThermal_eq_descendantEuler hβ,
    partitionFunction_thermalPoint]

/-- The complete character expansion is a convergent sum over precisely the
full-state labels appearing in the smooth entropy observable. -/
theorem hasSum_fullState_partitionFunction {c β : ℝ} {s : GapFamily.Spectrum}
    (hs : GapFamily.TorusAdmissible c s) (hβ : 0 < β) :
    HasSum (fun v : StateLevel s => (stateThermalTerm β c s v : ℂ))
      (GapFamily.partitionFunction c s (thermalPoint β hβ)) := by
  rw [← stateThermal_eq_partitionFunction hs hβ]
  exact (summable_stateThermalTerm hs hβ).hasSum.map
    Complex.ofRealHom Complex.continuous_ofReal

end BTZEntropy
