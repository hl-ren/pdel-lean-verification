import PdelBasic.Energy
import PdelEulerian.Energy
import PdelBridge.Vectors

noncomputable section
open Set MeasureTheory
namespace PdelBridge

/-- Newton exchange in the Layer-2 reservoir theorem has exactly the sign
and entropy production of the Layer-1 two-temperature exchange identity. -/
theorem reservoir_exchange_via_layer1 (M : PdelBasic.Material) (P : PdelBasic.Path)
    (L : PdelBasic.Loads) {a b : ℝ} (hab : a < b)
    (hst : PdelBasic.Stationary M P L a b) {t bath conductance : ℝ}
    (ht : t ∈ Icc a b) (hb : 0 < bath)
    (hq : L.heatOut t = conductance * (P.theta t - bath)) :
    deriv P.entropy t + L.heatOut t / bath =
      PdelBasic.dissipation M (P.v t) / P.theta t +
        conductance * (P.theta t - bath) * (1 / bath - 1 / P.theta t) := by
  rw [PdelMHD.exchange_entropy_identity conductance bath (P.theta t)
    (ne_of_gt hb) (ne_of_gt (P.theta_pos t))]
  rw [mul_comm bath (P.theta t)]
  exact PdelBasic.reservoir_entropy_identity M P L hab hst ht hb hq

theorem reservoir_nonnegative_via_layer1 (M : PdelBasic.Material) (P : PdelBasic.Path)
    (L : PdelBasic.Loads) {a b : ℝ} (hab : a < b)
    (hst : PdelBasic.Stationary M P L a b) {t bath conductance : ℝ}
    (ht : t ∈ Icc a b) (hb : 0 < bath) (hc : 0 ≤ conductance)
    (hq : L.heatOut t = conductance * (P.theta t - bath)) :
    0 ≤ deriv P.entropy t + L.heatOut t / bath := by
  rw [reservoir_exchange_via_layer1 M P L hab hst ht hb hq]
  exact add_nonneg
    (div_nonneg (PdelBasic.dissipation_nonnegative M (P.v t)) (P.theta_pos t).le)
    (PdelMHD.exchange_entropy_nonnegative conductance bath (P.theta t) hc hb (P.theta_pos t))

def basicPort (M : PdelBasic.Material) (P : PdelBasic.Path) (L : PdelBasic.Loads)
    (a b : ℝ) : ℝ := ∫ t in a..b, L.force t * P.v t - L.heatOut t

def eulerianEnergyChange (Q : PdelEulerian.Box) (G : PdelEulerian.Gas)
    (P : PdelEulerian.Fields) : ℝ :=
  Q.sliceEnergy (P.totalEnergy G) (Q.hi 0) - Q.sliceEnergy (P.totalEnergy G) (Q.lo 0)

def eulerianOutwardPort (Q : PdelEulerian.Box) (G : PdelEulerian.Gas)
    (K : PdelEulerian.Transport) (P : PdelEulerian.Fields) : ℝ :=
  Q.spatialBoundaryFlux (P.totalEnergyFlux G K)

/-- Connect two already-derived finite budgets without asserting that their
states, test spaces, or mechanical equations are identical. -/
theorem coupled_finite_energy_budget (M : PdelBasic.Material) (P : PdelBasic.Path)
    (L : PdelBasic.Loads) (Q : PdelEulerian.Box) (G : PdelEulerian.Gas)
    (K : PdelEulerian.Transport) (U : PdelEulerian.Fields)
    (F : PdelEulerian.MaterialChart U.velocity) (t0 : ℝ)
    (hbasic : PdelBasic.Stationary M P L (Q.lo 0) (Q.hi 0))
    (hmass : PdelEulerian.MassAdmissible Q U)
    (heuler : PdelEulerian.Stationary Q G K U F t0) :
    (PdelBasic.totalEnergy M P (Q.hi 0) - PdelBasic.totalEnergy M P (Q.lo 0)) +
      eulerianEnergyChange Q G U =
        basicPort M P L (Q.lo 0) (Q.hi 0) - eulerianOutwardPort Q G K U := by
  have hb := PdelBasic.finite_interval_energy_balance M P L (Q.strict 0) hbasic
  have he := PdelEulerian.integrated_energy_from_stationarity Q G K U F t0 hmass heuler
  change eulerianEnergyChange Q G U + eulerianOutwardPort Q G K U = 0 at he
  change _ = basicPort M P L (Q.lo 0) (Q.hi 0) at hb
  linarith

/-- All three layers participate: the two actual stationary systems supply
their finite budgets and the Layer-1 port algebra cancels the exchanged energy.
`exchange` is an integrated interface power, not an assumed field equation. -/
theorem three_layer_exchange_budget (M : PdelBasic.Material) (P : PdelBasic.Path)
    (L : PdelBasic.Loads) (Q : PdelEulerian.Box) (G : PdelEulerian.Gas)
    (K : PdelEulerian.Transport) (U : PdelEulerian.Fields)
    (F : PdelEulerian.MaterialChart U.velocity) (t0 basicExternal eulerExternal exchange : ℝ)
    (hbasic : PdelBasic.Stationary M P L (Q.lo 0) (Q.hi 0))
    (hmass : PdelEulerian.MassAdmissible Q U)
    (heuler : PdelEulerian.Stationary Q G K U F t0)
    (hbport : basicPort M P L (Q.lo 0) (Q.hi 0) = basicExternal + exchange)
    (heport : -eulerianOutwardPort Q G K U = eulerExternal - exchange) :
    (PdelBasic.totalEnergy M P (Q.hi 0) - PdelBasic.totalEnergy M P (Q.lo 0)) +
      eulerianEnergyChange Q G U = basicExternal + eulerExternal := by
  rw [coupled_finite_energy_budget M P L Q G K U F t0 hbasic hmass heuler,
    sub_eq_add_neg, hbport, heport]
  exact PdelMHD.exchange_energy_cancellation basicExternal eulerExternal exchange

theorem closed_three_layer_energy (M : PdelBasic.Material) (P : PdelBasic.Path)
    (L : PdelBasic.Loads) (Q : PdelEulerian.Box) (G : PdelEulerian.Gas)
    (K : PdelEulerian.Transport) (U : PdelEulerian.Fields)
    (F : PdelEulerian.MaterialChart U.velocity) (t0 : ℝ)
    (hbasic : PdelBasic.Stationary M P L (Q.lo 0) (Q.hi 0))
    (hmass : PdelEulerian.MassAdmissible Q U)
    (heuler : PdelEulerian.Stationary Q G K U F t0)
    (hinterface : basicPort M P L (Q.lo 0) (Q.hi 0) = eulerianOutwardPort Q G K U) :
    (PdelBasic.totalEnergy M P (Q.hi 0) - PdelBasic.totalEnergy M P (Q.lo 0)) +
      eulerianEnergyChange Q G U = 0 := by
  rw [coupled_finite_energy_budget M P L Q G K U F t0 hbasic hmass heuler,
    hinterface, sub_self]

end PdelBridge
