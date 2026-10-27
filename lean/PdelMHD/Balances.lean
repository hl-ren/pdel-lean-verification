import PdelMHD.PassiveTensor

/-!
# Algebraic cores of the thermal, power-history and boundary identities

Each statement is explicitly algebraic. The analytic identification of a
variable with a time-dependent power is handled by the SymPy time-derivative
checks, not silently assumed to have been proved in Lean here.
-/
namespace PdelMHD

theorem effective_pressure (b2 p g : ℝ) :
    b2 * (12*p-g)/9 - b2*(3*p-g)/9 = b2*p := by ring

theorem density_numerator_positive (p g : ℝ) (hg : 0 < g) (hp : g/3 < p) :
    0 < 12*p-g := by linarith

theorem bulk_numerator_positive (p g : ℝ) (hp : g/3 < p) :
    0 < 3*p-g := by linarith

theorem density_positive (b2 cv T p g : ℝ)
    (hb : 0 < b2) (hc : 0 < cv) (hT : 0 < T)
    (hg : 0 < g) (hp : g/3 < p) :
    0 < b2*(12*p-g)/(6*cv*T) := by
  exact div_pos (mul_pos hb (density_numerator_positive p g hg hp)) (by positivity)

theorem dissipative_power_sum (k b2 p g : ℝ) :
    k*b2*g + (4/3:ℝ)*k*b2*(3*p-g) = k*b2*(12*p-g)/3 := by ring

theorem joule_coefficient_positive (k b2 g : ℝ)
    (hk : 0 < k) (hb : 0 < b2) (hg : 0 < g) : 0 < k*b2*g := by positivity

theorem viscous_coefficient_positive (k b2 p g : ℝ)
    (hk : 0 < k) (hb : 0 < b2) (hp : g/3 < p) :
    0 < (4/3:ℝ)*k*b2*(3*p-g) := by
  have hm := bulk_numerator_positive p g hp
  positivity

theorem thermal_coefficient_balance (k b2 p g : ℝ) :
    (1/2:ℝ)*4*k*(b2*(12*p-g)/6) =
      k*b2*g + (4/3:ℝ)*k*b2*(3*p-g) := by ring

/-- y denotes a^(-3/2); no differentiability statement is asserted here. -/
theorem reference_history_sum (b2 p g y : ℝ) :
    b2*g/6*(1-y) + (2/9:ℝ)*b2*(3*p-g)*(1-y) =
      (b2*(12*p-g)/6)/3*(1-y) := by ring

theorem reference_internal_budget (b2 p g y : ℝ) :
    b2*g/6*(1-y) + (2/9:ℝ)*b2*(3*p-g)*(1-y)
      - (4/3:ℝ)*(b2*(12*p-g)/6)*(1-y) =
      (b2*(12*p-g)/6)*(y-1) := by ring

theorem boundary_power_sum (k b2 Ip Ig IB : ℝ) :
    4*k*b2*(3*Ip+IB/2) + k*b2*(IB-Ig) =
      k*b2*(12*Ip-Ig+3*IB) := by ring

theorem energy_coefficient_balance (k b2 Ip Ig IB : ℝ) :
    6*k*b2*((12*Ip-Ig)/6+IB/2) =
      4*k*b2*(3*Ip+IB/2) + k*b2*(IB-Ig) := by ring

theorem exchange_energy_cancellation (DJ DV Q : ℝ) :
    (DJ+Q)+(DV-Q)=DJ+DV := by ring

theorem exchange_entropy_identity (G Te Ti : ℝ)
    (he : Te ≠ 0) (hi : Ti ≠ 0) :
    G*(Ti-Te)*(1/Te-1/Ti) = G*(Ti-Te)^2/(Te*Ti) := by
  field_simp [he,hi] <;> ring

theorem exchange_entropy_nonnegative (G Te Ti : ℝ)
    (hG : 0 ≤ G) (he : 0 < Te) (hi : 0 < Ti) :
    0 ≤ G*(Ti-Te)*(1/Te-1/Ti) := by
  rw [exchange_entropy_identity G Te Ti (ne_of_gt he) (ne_of_gt hi)]
  exact div_nonneg (mul_nonneg hG (sq_nonneg _)) (le_of_lt (mul_pos he hi))

/-- q denotes a^(5/6), T denotes the positive mean temperature. -/
theorem two_temperature_mean (T r q : ℝ) :
    (T*r*q + T*(2-r*q))/2=T := by ring

theorem two_temperature_gap_positive (T r q : ℝ)
    (hT : 0 < T) (hrq : r*q < 1) :
    0 < T*(2-r*q)-T*r*q := by
  have h := mul_pos hT (sub_pos.mpr hrq)
  nlinarith

theorem endpoint_numerator_positive (p g : ℝ)
    (hg : 0 < g) (hp : g/3 < p) : (48*p-13*g)/9 > g/3 := by linarith

theorem endpoint_power_positive (k b2 decay p g : ℝ)
    (hk : 0 < k) (hb : 0 < b2) (hd : 0 < decay)
    (hg : 0 < g) (hp : g/3 < p) :
    0 < k*b2*decay*((48*p-13*g)/9) := by
  have hN : 0 < (48*p-13*g)/9 := by
    have h := endpoint_numerator_positive p g hg hp
    linarith
  positivity

/-- This is the finite-coefficient obstruction, not the full pole asymptotics. -/
theorem no_finite_exchange_at_equal_temperatures (T Q : ℝ) (hQ : 0 < Q) :
    ∀ G : ℝ, G*(T-T) ≠ Q := by
  intro G
  simpa using (ne_of_lt hQ)

/-- Positivity of the stated scalar-obstruction expression only.
The derivation of this expression from the Cartesian seed is not formalized. -/
theorem scalar_obstruction_positive (x k lam c : ℝ)
    (hx : 0 < x) (hk : 0 < k) (hl : 0 < lam) (hc : 0 < c) :
    0 < 16*x^3*c/(lam*k*(lam^2+4*x^2)^2) := by positivity

theorem lorentz_power_split (J E v B : V3) :
    dot J E - dot v (cross J B) = dot J E + dot J (cross v B) := by
  dsimp [dot, cross]
  ring

end PdelMHD
