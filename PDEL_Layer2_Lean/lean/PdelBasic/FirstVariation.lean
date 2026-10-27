import PdelBasic.History

/-!
# From a state--history functional to its complete mixed first variation

`mixedDensity` is an explicit finite perturbation REALIZING THE DECLARED
PDEL DIFFERENTIAL. Its history integrands are frozen at the original path.
The term linear in the variation parameter representing viscous virtual work
is the weak spending lift; it is not inferred from an upper-limit derivative.
This distinction is part of the statement, not hidden in the proof.
-/
noncomputable section
open MeasureTheory Set
open scoped Topology Interval
namespace PdelBasic

/-- Regularity and kinematics only: no dynamical or thermodynamic equations. -/
structure Path where
  x : ℝ → ℝ
  v : ℝ → ℝ
  acc : ℝ → ℝ
  theta : ℝ → ℝ
  entropy : ℝ → ℝ
  x_c1 : ContDiff ℝ 1 x
  v_c1 : ContDiff ℝ 1 v
  acc_c1 : ContDiff ℝ 1 acc
  theta_c1 : ContDiff ℝ 1 theta
  entropy_c1 : ContDiff ℝ 1 entropy
  dx : ∀ t, HasDerivAt x (v t) t
  dv : ∀ t, HasDerivAt v (acc t) t
  theta_pos : ∀ t, 0 < theta t

structure Loads where
  force : ℝ → ℝ
  heatOut : ℝ → ℝ
  force_c1 : ContDiff ℝ 1 force
  heatOut_cont : Continuous heatOut

/-- Mechanical endpoints are fixed; thermal and entropy tests are independent. -/
structure Variation (t0 t1 : ℝ) where
  h : ℝ → ℝ
  h_c1 : ContDiff ℝ 1 h
  left : h t0 = 0
  right : h t1 = 0
  temperatureTest : ℝ → ℝ
  temperatureTest_cont : Continuous temperatureTest
  entropySelector : ℝ → ℝ
  entropySelector_cont : Continuous entropySelector

theorem path_theta_hasDerivAt (P : Path) (t : ℝ) :
    HasDerivAt P.theta (deriv P.theta t) t :=
  (P.theta_c1.differentiable (by norm_num) t).hasDerivAt

theorem path_entropy_hasDerivAt (P : Path) (t : ℝ) :
    HasDerivAt P.entropy (deriv P.entropy t) t :=
  (P.entropy_c1.differentiable (by norm_num) t).hasDerivAt

theorem path_dissipation_continuous (M : Material) (P : Path) :
    Continuous (fun t => dissipation M (P.v t)) := by
  dsimp [dissipation, viscousForce]
  exact (continuous_const.mul P.v_c1.continuous).mul P.v_c1.continuous

theorem path_entropyState_continuous (M : Material) (P : Path) :
    Continuous (fun t => entropyState M (P.x t) (P.theta t)) := by
  have hlog : Continuous (fun t => Real.log (P.theta t / M.thetaRef)) :=
    (P.theta_c1.continuous.div_const M.thetaRef).log
      (fun t => div_ne_zero (ne_of_gt (P.theta_pos t)) (ne_of_gt M.thetaRef_pos))
  exact (continuous_const.mul P.x_c1.continuous).add (continuous_const.mul hlog)

def stateHistoryDensity (M : Material) (P : Path) (L : Loads) (t0 t : ℝ) : ℝ :=
  kinetic M (P.v t) - freeEnergy M (P.x t) (P.theta t) - P.theta t * P.entropy t -
  powerHistory L.heatOut t0 t + powerHistory (fun u => dissipation M (P.v u)) t0 t +
  L.force t * P.x t

def action (M : Material) (P : Path) (L : Loads) (t0 t1 : ℝ) : ℝ :=
  ∫ t in t0..t1, stateHistoryDensity M P L t0 t

/-- The state--history integral is a genuine integrable real function on each finite interval. -/
theorem stateHistoryDensity_continuous (M : Material) (P : Path) (L : Loads) (t0 : ℝ) :
    Continuous (stateHistoryDensity M P L t0) := by
  have hx := P.x_c1.continuous
  have hv := P.v_c1.continuous
  have hT := P.theta_c1.continuous
  have hs := P.entropy_c1.continuous
  have hf := L.force_c1.continuous
  have hlog : Continuous (fun t => Real.log (P.theta t / M.thetaRef)) :=
    (hT.div_const M.thetaRef).log
      (fun t => div_ne_zero (ne_of_gt (P.theta_pos t)) (ne_of_gt M.thetaRef_pos))
  have hQ := powerHistory_continuous L.heatOut_cont t0
  have hD := powerHistory_continuous (path_dissipation_continuous M P) t0
  unfold stateHistoryDensity kinetic freeEnergy
  fun_prop

theorem action_integrable (M : Material) (P : Path) (L : Loads) (t0 t1 : ℝ) :
    IntervalIntegrable (stateHistoryDensity M P L t0) volume t0 t1 :=
  (stateHistoryDensity_continuous M P L t0).intervalIntegrable t0 t1

/-- A local affine state jet; past powers are not recomputed on this jet. -/
def mixedDensity (M : Material) (P : Path) (L : Loads) {t0 t1 : ℝ}
    (V : Variation t0 t1) (e t : ℝ) : ℝ :=
  kinetic M (P.v t + e * deriv V.h t) -
  freeEnergy M (P.x t + e * V.h t) (P.theta t + e * V.temperatureTest t) -
  (P.theta t + e * V.temperatureTest t) *
    (P.entropy t + e * (deriv P.entropy t * V.entropySelector t)) -
  powerHistory L.heatOut t0 (t + e * V.entropySelector t) +
  powerHistory (fun u => dissipation M (P.v u)) t0 (t + e * V.entropySelector t) -
  e * (viscousForce M (P.v t) * V.h t) +
  L.force t * (P.x t + e * V.h t)

def mixedAction (M : Material) (P : Path) (L : Loads) {t0 t1 : ℝ}
    (V : Variation t0 t1) (e : ℝ) : ℝ :=
  ∫ t in t0..t1, mixedDensity M P L V e t

/-- The PDEL differential is the integral of its prescribed local operations. -/
def firstVariation (M : Material) (P : Path) (L : Loads) {t0 t1 : ℝ}
    (V : Variation t0 t1) : ℝ :=
  ∫ t in t0..t1, deriv (fun e => mixedDensity M P L V e t) 0

def mechanicalResidual (M : Material) (P : Path) (L : Loads) (t : ℝ) : ℝ :=
  M.mass * P.acc t + elasticForce M (P.x t) (P.theta t) +
    viscousForce M (P.v t) - L.force t

def thermalResidual (M : Material) (P : Path) (t : ℝ) : ℝ :=
  P.entropy t - entropyState M (P.x t) (P.theta t)

def entropyResidual (M : Material) (P : Path) (L : Loads) (t : ℝ) : ℝ :=
  P.theta t * deriv P.entropy t + L.heatOut t - dissipation M (P.v t)

-- This density is computed from the preceding derivative, not its definition.
def weakDensity (M : Material) (P : Path) (L : Loads) {t0 t1 : ℝ}
    (V : Variation t0 t1) (t : ℝ) : ℝ :=
  M.mass * P.v t * deriv V.h t -
  (elasticForce M (P.x t) (P.theta t) + viscousForce M (P.v t) - L.force t) * V.h t -
  thermalResidual M P t * V.temperatureTest t -
  entropyResidual M P L t * V.entropySelector t

theorem mixedDensity_at_zero (M : Material) (P : Path) (L : Loads)
    {t0 t1 : ℝ} (V : Variation t0 t1) (t : ℝ) :
    mixedDensity M P L V 0 t = stateHistoryDensity M P L t0 t := by
  simp [mixedDensity, stateHistoryDensity]

theorem mixedAction_at_zero (M : Material) (P : Path) (L : Loads)
    {t0 t1 : ℝ} (V : Variation t0 t1) :
    mixedAction M P L V 0 = action M P L t0 t1 := by
  unfold mixedAction action
  apply intervalIntegral.integral_congr
  intro t _
  exact mixedDensity_at_zero M P L V t

theorem affineJet_hasDerivAt (value direction e : ℝ) :
    HasDerivAt (fun r : ℝ => value + r * direction) direction e := by
  simpa using ((hasDerivAt_id e).mul_const direction).const_add value

/-- The velocity jet used in the variation is induced by a varied motion. -/
theorem varied_motion_hasDerivAt (P : Path) {t0 t1 : ℝ}
    (V : Variation t0 t1) (e t : ℝ) :
    HasDerivAt (fun u => P.x u + e * V.h u)
      (P.v t + e * deriv V.h t) t := by
  exact (P.dx t).add
    (((V.h_c1.differentiable (by norm_num) t).hasDerivAt).const_mul e)

/-- The entropy selector is the first-order derivative of the REAL realized path. -/
theorem entropy_path_channel_derivative (P : Path) (t selector : ℝ) :
    HasDerivAt (fun e => P.entropy (t + e * selector))
      (deriv P.entropy t * selector) 0 := by
  have he := affineJet_hasDerivAt t selector 0
  simpa only [zero_mul, add_zero] using
    (path_entropy_hasDerivAt P (t + (0 : ℝ) * selector)).comp 0 he

/-- Genuine directional derivative of the complete explicit mixed density. -/
theorem mixedDensity_hasDerivAt (M : Material) (P : Path) (L : Loads)
    {t0 t1 : ℝ} (V : Variation t0 t1) (t : ℝ) :
    HasDerivAt (fun e => mixedDensity M P L V e t) (weakDensity M P L V t) 0 := by
  have hx := affineJet_hasDerivAt (P.x t) (V.h t) 0
  have hv := affineJet_hasDerivAt (P.v t) (deriv V.h t) 0
  have hT := affineJet_hasDerivAt (P.theta t) (V.temperatureTest t) 0
  have hs := affineJet_hasDerivAt (P.entropy t)
    (deriv P.entropy t * V.entropySelector t) 0
  have hp := freeEnergy_hasDerivAt M hx hT (by simpa using P.theta_pos t)
  have hk := kinetic_hasDerivAt M hv
  have hq := endpoint_channel_derivative L.heatOut_cont t0 t (V.entropySelector t)
  have hd := endpoint_channel_derivative (path_dissipation_continuous M P)
    t0 t (V.entropySelector t)
  have hw := (hasDerivAt_id (0 : ℝ)).mul_const (viscousForce M (P.v t) * V.h t)
  have hf := hx.const_mul (L.force t)
  convert (((((hk.sub hp).sub (hT.mul hs)).sub hq).add hd).sub hw).add hf using 1 <;>
    dsimp [mixedDensity, weakDensity, thermalResidual, entropyResidual] <;>
    simp only [zero_mul, add_zero, one_mul] <;> ring

theorem firstVariation_raw (M : Material) (P : Path) (L : Loads)
    {t0 t1 : ℝ} (V : Variation t0 t1) :
    firstVariation M P L V = ∫ t in t0..t1, weakDensity M P L V t := by
  unfold firstVariation
  apply intervalIntegral.integral_congr
  intro t _
  exact (mixedDensity_hasDerivAt M P L V t).deriv

theorem mechanicalResidual_c1 (M : Material) (P : Path) (L : Loads) :
    ContDiff ℝ 1 (mechanicalResidual M P L) := by
  have hx := P.x_c1
  have hv := P.v_c1
  have ha := P.acc_c1
  have hT := P.theta_c1
  have hf := L.force_c1
  unfold mechanicalResidual elasticForce viscousForce
  fun_prop

theorem thermalResidual_continuous (M : Material) (P : Path) :
    Continuous (thermalResidual M P) :=
  P.entropy_c1.continuous.sub (path_entropyState_continuous M P)

theorem entropyResidual_continuous (M : Material) (P : Path) (L : Loads) :
    Continuous (entropyResidual M P L) := by
  have hs : Continuous (deriv P.entropy) := P.entropy_c1.continuous_deriv (by norm_num)
  exact ((P.theta_c1.continuous.mul hs).add L.heatOut_cont).sub
    (path_dissipation_continuous M P)

theorem weakDensity_continuous (M : Material) (P : Path) (L : Loads)
    {t0 t1 : ℝ} (V : Variation t0 t1) : Continuous (weakDensity M P L V) := by
  have hv := P.v_c1.continuous
  have hx := P.x_c1.continuous
  have hT := P.theta_c1.continuous
  have hf := L.force_c1.continuous
  have hh := V.h_c1.continuous
  have hdh : Continuous (deriv V.h) := V.h_c1.continuous_deriv (by norm_num)
  have hz := V.temperatureTest_cont
  have hw := V.entropySelector_cont
  have hrt := thermalResidual_continuous M P
  have hrs := entropyResidual_continuous M P L
  unfold weakDensity elasticForce viscousForce
  fun_prop

/-- Full first variation AFTER a proved integration-by-parts step. -/
theorem firstVariation_residual (M : Material) (P : Path) (L : Loads)
    {t0 t1 : ℝ} (V : Variation t0 t1) :
    firstVariation M P L V =
      -(∫ t in t0..t1, mechanicalResidual M P L t * V.h t) -
       (∫ t in t0..t1, thermalResidual M P t * V.temperatureTest t) -
       (∫ t in t0..t1, entropyResidual M P L t * V.entropySelector t) := by
  have hv := P.v_c1.continuous
  have ha := P.acc_c1.continuous
  have hx := P.x_c1.continuous
  have hT := P.theta_c1.continuous
  have hf := L.force_c1.continuous
  have hh := V.h_c1.continuous
  have hdh : Continuous (deriv V.h) := V.h_c1.continuous_deriv (by norm_num)
  have hrest : Continuous (fun t =>
      (elasticForce M (P.x t) (P.theta t) + viscousForce M (P.v t) - L.force t) * V.h t) := by
    dsimp [elasticForce, viscousForce]
    fun_prop
  have hA : IntervalIntegrable (fun t => M.mass * P.v t * deriv V.h t) volume t0 t1 :=
    ((continuous_const.mul hv).mul hdh).intervalIntegrable t0 t1
  have hB := hrest.intervalIntegrable (μ := volume) t0 t1
  have hC := ((thermalResidual_continuous M P).mul V.temperatureTest_cont).intervalIntegrable
    (μ := volume) t0 t1
  have hD := ((entropyResidual_continuous M P L).mul V.entropySelector_cont).intervalIntegrable
    (μ := volume) t0 t1
  have hparts : (∫ t in t0..t1, M.mass * P.v t * deriv V.h t) =
      -(∫ t in t0..t1, M.mass * P.acc t * V.h t) := by
    have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun t => M.mass * P.v t) (v := V.h)
      (u' := fun t => M.mass * P.acc t) (v' := deriv V.h)
      (a := t0) (b := t1)
      (fun t _ => (P.dv t).const_mul M.mass)
      (fun t _ => (V.h_c1.differentiable (by norm_num) t).hasDerivAt)
      ((continuous_const.mul ha).intervalIntegrable t0 t1)
      (hdh.intervalIntegrable t0 t1)
    simpa only [V.left, V.right, mul_zero, sub_zero, zero_sub] using hp
  have hcombine : (∫ t in t0..t1, mechanicalResidual M P L t * V.h t) =
      (∫ t in t0..t1, M.mass * P.acc t * V.h t) +
      (∫ t in t0..t1,
        (elasticForce M (P.x t) (P.theta t) + viscousForce M (P.v t) - L.force t) * V.h t) := by
    calc
      _ = ∫ t in t0..t1, M.mass * P.acc t * V.h t +
          (elasticForce M (P.x t) (P.theta t) + viscousForce M (P.v t) - L.force t) * V.h t := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [mechanicalResidual]
        ring
      _ = _ := intervalIntegral.integral_add
        (((continuous_const.mul ha).mul hh).intervalIntegrable t0 t1) hB
  rw [firstVariation_raw]
  unfold weakDensity
  rw [intervalIntegral.integral_sub ((hA.sub hB).sub hC) hD,
    intervalIntegral.integral_sub (hA.sub hB) hC,
    intervalIntegral.integral_sub hA hB, hparts, hcombine]
  ring

end PdelBasic
