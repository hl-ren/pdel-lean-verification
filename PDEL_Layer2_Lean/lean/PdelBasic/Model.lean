import Mathlib

/-!
# A thermo-viscoelastic material with one mechanical degree of freedom

This is the scalar, unit-reference-volume specialization of the supplied
`PDEL basic example 3.md`, Example I.  `heatOut` below is NET outward thermal
power (outward heat flux minus imposed heat supply), not a dissipation.
The coupling `beta` can have either sign.  Entropy has an arbitrary reference.
No equations of motion or thermal conjugacy are fields of `Material`.
-/

noncomputable section
open scoped Topology
namespace PdelBasic

structure Material where
  mass : ℝ
  stiffness : ℝ
  beta : ℝ
  capacity : ℝ
  thetaRef : ℝ
  viscosity : ℝ
  mass_pos : 0 < mass
  stiffness_pos : 0 < stiffness
  capacity_pos : 0 < capacity
  thetaRef_pos : 0 < thetaRef
  viscosity_nonneg : 0 ≤ viscosity

-- Displacement and strain coincide in this normalized one-mode model.
def freeEnergy (M : Material) (x theta : ℝ) : ℝ :=
  M.stiffness / 2 * x ^ 2 - M.beta * (theta - M.thetaRef) * x +
  M.capacity * ((theta - M.thetaRef) - theta * Real.log (theta / M.thetaRef))

def elasticForce (M : Material) (x theta : ℝ) : ℝ :=
  M.stiffness * x - M.beta * (theta - M.thetaRef)

-- A candidate expression, proved below to be -partial_theta(freeEnergy).
def entropyState (M : Material) (x theta : ℝ) : ℝ :=
  M.beta * x + M.capacity * Real.log (theta / M.thetaRef)

def viscousForce (M : Material) (v : ℝ) : ℝ := M.viscosity * v

def dissipation (M : Material) (v : ℝ) : ℝ := viscousForce M v * v

def kinetic (M : Material) (v : ℝ) : ℝ := M.mass / 2 * v ^ 2

-- Keep theta and entropy independent until stationarity is used.
def mixedInternal (M : Material) (x theta entropy : ℝ) : ℝ :=
  freeEnergy M x theta + theta * entropy

theorem viscous_same_response (M : Material) (v h : ℝ) :
    viscousForce M v * (v * h) = dissipation M v * h := by
  unfold dissipation
  ring

theorem dissipation_nonnegative (M : Material) (v : ℝ) :
    0 ≤ dissipation M v := by
  dsimp [dissipation, viscousForce]
  nlinarith [mul_nonneg M.viscosity_nonneg (sq_nonneg v)]

theorem dissipation_positive (M : Material) (hv : 0 < M.viscosity)
    {v : ℝ} (hvn : v ≠ 0) : 0 < dissipation M v := by
  dsimp [dissipation, viscousForce]
  nlinarith [mul_pos hv (sq_pos_of_ne_zero hvn)]

/-- Actual calculus of the logarithmic state, not an assumed Gibbs identity. -/
theorem freeEnergy_hasDerivAt (M : Material) {x theta : ℝ → ℝ}
    {t dx dtheta : ℝ} (hx : HasDerivAt x dx t)
    (hT : HasDerivAt theta dtheta t) (hpos : 0 < theta t) :
    HasDerivAt (fun u => freeEnergy M (x u) (theta u))
      (elasticForce M (x t) (theta t) * dx -
        entropyState M (x t) (theta t) * dtheta) t := by
  have hlog : HasDerivAt (fun u => Real.log (theta u / M.thetaRef))
      (dtheta / theta t) t := by
    convert (hT.div_const M.thetaRef).log
      (div_ne_zero (ne_of_gt hpos) (ne_of_gt M.thetaRef_pos)) using 1 <;>
      field_simp [ne_of_gt hpos, ne_of_gt M.thetaRef_pos] <;> ring
  have h := ((hx.pow 2).const_mul (M.stiffness / 2)).sub
    (((hT.sub_const M.thetaRef).const_mul M.beta).mul hx)
  have hthermal := ((hT.sub_const M.thetaRef).sub (hT.mul hlog)).const_mul M.capacity
  convert h.add hthermal using 1 <;>
    dsimp [freeEnergy, elasticForce, entropyState] <;>
    field_simp [ne_of_gt hpos, ne_of_gt M.thetaRef_pos] <;> ring

theorem freeEnergy_x_derivative (M : Material) (x theta : ℝ) (hpos : 0 < theta) :
    HasDerivAt (fun y => freeEnergy M y theta) (elasticForce M x theta) x := by
  simpa using freeEnergy_hasDerivAt M (hasDerivAt_id x)
    (hasDerivAt_const x theta) hpos

theorem freeEnergy_theta_derivative (M : Material) (x theta : ℝ)
    (hpos : 0 < theta) :
    HasDerivAt (fun T => freeEnergy M x T) (-entropyState M x theta) theta := by
  simpa using freeEnergy_hasDerivAt M (hasDerivAt_const theta x)
    (hasDerivAt_id theta) hpos

theorem entropy_is_negative_thermal_derivative (M : Material) (x theta : ℝ)
    (hpos : 0 < theta) :
    entropyState M x theta = -deriv (fun T => freeEnergy M x T) theta := by
  rw [(freeEnergy_theta_derivative M x theta hpos).deriv]
  ring

theorem entropyState_hasDerivAt (M : Material) {x theta : ℝ → ℝ}
    {t dx dtheta : ℝ} (hx : HasDerivAt x dx t)
    (hT : HasDerivAt theta dtheta t) (hpos : 0 < theta t) :
    HasDerivAt (fun u => entropyState M (x u) (theta u))
      (M.beta * dx + M.capacity * dtheta / theta t) t := by
  have hlog : HasDerivAt (fun u => Real.log (theta u / M.thetaRef))
      (dtheta / theta t) t := by
    convert (hT.div_const M.thetaRef).log
      (div_ne_zero (ne_of_gt hpos) (ne_of_gt M.thetaRef_pos)) using 1 <;>
      field_simp [ne_of_gt hpos, ne_of_gt M.thetaRef_pos] <;> ring
  convert (hx.const_mul M.beta).add (hlog.const_mul M.capacity) using 1 <;>
    dsimp [entropyState] <;> ring

theorem mixedInternal_chain_rule (M : Material) {x theta entropy : ℝ → ℝ}
    {t dx dtheta ds : ℝ} (hx : HasDerivAt x dx t)
    (hT : HasDerivAt theta dtheta t) (hs : HasDerivAt entropy ds t)
    (hpos : 0 < theta t) :
    HasDerivAt (fun u => mixedInternal M (x u) (theta u) (entropy u))
      (elasticForce M (x t) (theta t) * dx +
        (entropy t - entropyState M (x t) (theta t)) * dtheta + theta t * ds) t := by
  convert (freeEnergy_hasDerivAt M hx hT hpos).add (hT.mul hs) using 1 <;>
    dsimp [mixedInternal] <;> ring

/-- Simplification of internal energy is AFTER imposing conjugacy. -/
theorem internalEnergy_on_conjugacy (M : Material) (x theta : ℝ) :
    mixedInternal M x theta (entropyState M x theta) =
      M.stiffness / 2 * x ^ 2 + M.beta * M.thetaRef * x +
        M.capacity * (theta - M.thetaRef) := by
  dsimp [mixedInternal, freeEnergy, entropyState]
  ring

theorem kinetic_hasDerivAt (M : Material) {v : ℝ → ℝ} {t a : ℝ}
    (hv : HasDerivAt v a t) :
    HasDerivAt (fun u => kinetic M (v u)) (M.mass * v t * a) t := by
  convert (hv.pow 2).const_mul (M.mass / 2) using 1 <;>
    dsimp [kinetic] <;> ring

end PdelBasic
