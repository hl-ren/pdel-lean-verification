import PdelBridge
import PdelRevision3

/-! Validation-only interface checks. No original theorem or assumption is changed.
These checks do not construct a homologous MaterialChart or a toroidal field. -/
noncomputable section
namespace PdelIntegration
open PdelRevision3

theorem branch_dissipation_via_layer1 (kappa b p g t : ℝ) :
    branchJoulePower kappa b g t + branchViscousPower kappa b p g t =
      (kappa*b^2*(12*p-g)/3) * (expansionScale (4*kappa) t)^(-11/2 : ℝ) := by
  unfold branchJoulePower branchViscousPower
  rw [← add_mul, PdelMHD.dissipative_power_sum]

theorem reference_joule_history_uses_layer2 (C U t : ℝ) :
    referenceJouleHistory C U t = PdelBasic.powerHistory
      (fun s => (3*C*U/2)*(expansionScale U s)^(-5/2 : ℝ)) 0 t := rfl

theorem cumulative_heat_uses_layer2 (kappa b p g t : ℝ) :
    cumulativeIrreversibleHeat kappa b p g t =
      PdelBasic.powerHistory (referenceHeatRate kappa b p g) 0 t := rfl

theorem cumulative_work_uses_layer2 (kappa b p g t : ℝ) :
    cumulativePressureWork kappa b p g t =
      PdelBasic.powerHistory (referencePressureRate kappa b p g) 0 t := rfl

theorem nonmagnetic_rest_matches_bridge (G : PdelEulerian.Gas)
    (temp entropy : PdelEulerian.Scalar) (ht : ∀ p, 0 < temp p) :
    nonmagneticFields (PdelBridge.referenceState G temp entropy ht) 0 =
      PdelBridge.restFields G temp entropy ht 0 := rfl

end PdelIntegration
