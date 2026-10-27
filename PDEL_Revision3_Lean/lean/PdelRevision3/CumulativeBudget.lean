import Mathlib

noncomputable section
open Set MeasureTheory
namespace PdelRevision3

def expansionScale (U t : ℝ) : ℝ := 1 + U * t

theorem expansionScale_positive {U t : ℝ} (hU : 0 ≤ U) (ht : 0 ≤ t) :
    0 < expansionScale U t := by
  unfold expansionScale
  positivity

/-- Revision3 eq:powers and eq:thermalpressure, at a fixed material label.
The scale is eq:scale, U = 4 kappa. No field equation is an input. -/
def branchJoulePower (kappa b g t : ℝ) : ℝ :=
  kappa * b ^ 2 * g * (expansionScale (4*kappa) t) ^ (-11/2 : ℝ)

def branchViscousPower (kappa b p g t : ℝ) : ℝ :=
  (4/3 : ℝ) * kappa * b ^ 2 * (3*p-g) * (expansionScale (4*kappa) t) ^ (-11/2 : ℝ)

def branchPressure (kappa b p g t : ℝ) : ℝ :=
  b ^ 2 / 9 * (12*p-g) * (expansionScale (4*kappa) t) ^ (-9/2 : ℝ)

def referenceHeatRate (kappa b p g t : ℝ) : ℝ :=
  (expansionScale (4*kappa) t)^3 *
    (branchJoulePower kappa b g t + branchViscousPower kappa b p g t)

def referencePressureRate (kappa b p g t : ℝ) : ℝ :=
  (expansionScale (4*kappa) t)^3 * branchPressure kappa b p g t *
    (3*(4*kappa) / expansionScale (4*kappa) t)

def cumulativeIrreversibleHeat (kappa b p g t : ℝ) : ℝ :=
  ∫ s in (0)..t, referenceHeatRate kappa b p g s

def cumulativePressureWork (kappa b p g t : ℝ) : ℝ :=
  ∫ s in (0)..t, referencePressureRate kappa b p g s

theorem pressure_rate_four_heat (kappa b p g t : ℝ)
    (ha : 0 < expansionScale (4*kappa) t) :
    referencePressureRate kappa b p g t = 4 * referenceHeatRate kappa b p g t := by
  have hp : (expansionScale (4*kappa) t) ^ (-11/2 : ℝ) =
      (expansionScale (4*kappa) t) ^ (-9/2 : ℝ) / expansionScale (4*kappa) t := by
    rw [show (-11/2 : ℝ) = (-9/2 : ℝ) - 1 by norm_num, Real.rpow_sub ha, Real.rpow_one]
  unfold referencePressureRate referenceHeatRate branchPressure branchJoulePower branchViscousPower
  rw [hp]
  ring

theorem reference_heat_integrable (kappa b p g t : ℝ)
    (hk : 0 ≤ kappa) (ht : 0 ≤ t) :
    IntervalIntegrable (referenceHeatRate kappa b p g) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  have hs0 : 0 ≤ s := (uIcc_of_le ht ▸ hs).1
  have ha := expansionScale_positive (show 0 ≤ 4*kappa by positivity) hs0
  have hc : ContinuousAt (expansionScale (4*kappa)) s := by
    unfold expansionScale
    fun_prop
  have hr : ContinuousAt (fun s => (expansionScale (4*kappa) s) ^ (-11/2 : ℝ)) s :=
    hc.rpow_const (Or.inl (ne_of_gt ha))
  exact ((hc.pow 3).mul ((continuousAt_const.mul hr).add
    (continuousAt_const.mul hr))).continuousWithinAt

/-- Actual interval integrals of the prescribed branch powers, not an assumed
energy budget or an equality between names assigned to closed formulas. -/
theorem cumulative_pressure_four_irreversible (kappa b p g t : ℝ)
    (hk : 0 ≤ kappa) (ht : 0 ≤ t) :
    cumulativePressureWork kappa b p g t = 4 * cumulativeIrreversibleHeat kappa b p g t := by
  unfold cumulativePressureWork cumulativeIrreversibleHeat
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (uIcc_of_le ht ▸ hs).1
  exact pressure_rate_four_heat kappa b p g s
    (expansionScale_positive (show 0 ≤ 4*kappa by positivity) hs0)

end PdelRevision3
