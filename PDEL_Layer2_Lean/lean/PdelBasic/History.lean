import PdelBasic.Model

/-! Real interval integrals and their upper-endpoint derivatives. -/
noncomputable section
open MeasureTheory Set
open scoped Topology Interval
namespace PdelBasic

def powerHistory (power : ℝ → ℝ) (t0 t : ℝ) : ℝ :=
  ∫ u in t0..t, power u

theorem powerHistory_hasDerivAt {power : ℝ → ℝ} (hc : Continuous power)
    (t0 t : ℝ) : HasDerivAt (powerHistory power t0) (power t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable t0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem powerHistory_continuous {power : ℝ → ℝ} (hc : Continuous power) (t0 : ℝ) :
    Continuous (powerHistory power t0) := by
  exact continuous_iff_continuousAt.mpr (fun t =>
    (powerHistory_hasDerivAt hc t0 t).continuousAt)

theorem powerHistory_zero (power : ℝ → ℝ) (t0 : ℝ) :
    powerHistory power t0 t0 = 0 := by simp [powerHistory]

/-- The realized integrand is held fixed; only the endpoint moves. -/
theorem endpoint_channel_derivative {power : ℝ → ℝ} (hc : Continuous power)
    (t0 t selector : ℝ) :
    HasDerivAt (fun e => powerHistory power t0 (t + e * selector))
      (power t * selector) 0 := by
  have he : HasDerivAt (fun e : ℝ => t + e * selector) selector 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const selector).const_add t
  simpa only [zero_mul, add_zero] using
    (powerHistory_hasDerivAt hc t0 (t + (0 : ℝ) * selector)).comp 0 he

theorem endpoint_channel_formula {power : ℝ → ℝ} (hc : Continuous power)
    (t0 t selector : ℝ) :
    deriv (fun e => powerHistory power t0 (t + e * selector)) 0 = power t * selector :=
  (endpoint_channel_derivative hc t0 t selector).deriv

theorem powerHistory_nonnegative {power : ℝ → ℝ} (hpos : ∀ u, 0 ≤ power u)
    {t0 t : ℝ} (ht : t0 ≤ t) : 0 ≤ powerHistory power t0 t := by
  exact intervalIntegral.integral_nonneg_of_forall ht hpos

theorem powerHistory_additive {power : ℝ → ℝ} (hc : Continuous power)
    (a b c : ℝ) :
    powerHistory power a b + powerHistory power b c = powerHistory power a c := by
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a b) (hc.intervalIntegrable b c)

/-- The weak donor is a definition of PDEL, NOT a consequence of the FTC alone. -/
def spending (M : Material) (v displacementTest entropySelector : ℝ) : ℝ :=
  dissipation M v * entropySelector - viscousForce M v * displacementTest

theorem spending_realized_path (M : Material) (v ds dm : ℝ) :
    spending M v (v * dm) ds = dissipation M v * (ds - dm) := by
  dsimp [spending, dissipation]
  ring

theorem synchronized_spending_zero (M : Material) (v selector : ℝ) :
    spending M v (v * selector) selector = 0 := by
  rw [spending_realized_path]
  ring

end PdelBasic
