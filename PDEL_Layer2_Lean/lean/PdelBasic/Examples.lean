import PdelBasic.Energy

/-! Non-vacuity witness and a diagnostic for duplicating the heat receiver. -/
noncomputable section
open MeasureTheory Set
open scoped Topology Interval
namespace PdelBasic

def witnessMaterial : Material where
  mass := 1
  stiffness := 2
  beta := 1
  capacity := 3
  thetaRef := 1
  viscosity := 1
  mass_pos := by norm_num
  stiffness_pos := by norm_num
  capacity_pos := by norm_num
  thetaRef_pos := by norm_num
  viscosity_nonneg := by norm_num

/-- Driven deformation, NONZERO viscous heating, positive constant temperature. -/
def witnessPath : Path where
  x := fun t => t
  v := fun _ => 1
  acc := fun _ => 0
  theta := fun _ => 1
  entropy := fun t => t
  x_c1 := contDiff_id
  v_c1 := contDiff_const
  acc_c1 := contDiff_const
  theta_c1 := contDiff_const
  entropy_c1 := contDiff_id
  dx := fun t => hasDerivAt_id t
  dv := fun t => hasDerivAt_const t 1
  theta_pos := fun _ => by norm_num

def witnessLoads : Loads where
  force := fun t => 2 * t + 1
  heatOut := fun _ => 0
  force_c1 := by fun_prop
  heatOut_cont := continuous_const

theorem witness_governing (a b : ℝ) :
    GoverningOn witnessMaterial witnessPath witnessLoads a b := by
  intro t _
  have hd : deriv (fun u : ℝ => u) t = 1 := (hasDerivAt_id t).deriv
  simp [witnessMaterial, witnessPath, witnessLoads, elasticForce,
    viscousForce, entropyState, dissipation, hd]

theorem witness_stationary {a b : ℝ} (hab : a < b) :
    Stationary witnessMaterial witnessPath witnessLoads a b :=
  (pdel_basic_variational_theorem witnessMaterial witnessPath witnessLoads hab).mpr
    (witness_governing a b)

theorem witness_nonzero_dissipation (t : ℝ) :
    dissipation witnessMaterial (witnessPath.v t) = 1 := by
  norm_num [witnessMaterial, witnessPath, dissipation, viscousForce]

theorem witness_energy (t : ℝ) :
    totalEnergy witnessMaterial witnessPath t = 1 / 2 + t^2 + t := by
  dsimp [totalEnergy, kinetic, internalEnergy, mixedInternal, freeEnergy,
    witnessMaterial, witnessPath]
  norm_num <;> ring

/-- A duplicate receiver creates an extra energy source, not the correct balance. -/
theorem duplicate_heat_creates_energy (M : Material)
    (v acc stress theta ds heatOut force : ℝ)
    (hm : M.mass * acc + stress + viscousForce M v = force)
    (hbad : theta * ds + heatOut = 2 * dissipation M v) :
    M.mass * v * acc + stress * v + theta * ds =
      force * v - heatOut + dissipation M v := by
  have hp := congrArg (fun z : ℝ => z * v) hm
  dsimp [dissipation] at *
  nlinarith [hp, hbad]

end PdelBasic
