import PdelBasic.Energy
import PdelBridge.Tensor

noncomputable section
namespace PdelBridge

/-- A comparison material for the fixed-reference-density thermal sector.
The mechanical constants are explicit and do not assert a fluid/solid reduction. -/
def referenceMaterial (G : PdelEulerian.Gas) (viscosity : ℝ) (hv : 0 ≤ viscosity) :
    PdelBasic.Material where
  mass := 1
  stiffness := 1
  beta := 0
  capacity := G.rhoRef * G.cv
  thetaRef := G.tempRef
  viscosity := viscosity
  mass_pos := zero_lt_one
  stiffness_pos := zero_lt_one
  capacity_pos := mul_pos G.rhoRef_pos G.cv_pos
  thetaRef_pos := G.tempRef_pos
  viscosity_nonneg := hv

def referenceState (G : PdelEulerian.Gas) (temp entropy : PdelEulerian.Scalar)
    (ht : ∀ p, 0 < temp p) : PdelEulerian.ThermalState where
  rho := PdelEulerian.C G.rhoRef
  temp := temp
  entropy := entropy
  rho_pos := fun _ => G.rhoRef_pos
  temp_pos := ht

/-- Exact constitutive comparison: elastic storage and a constant energy datum
remain visible. No equality of the full mechanical models is asserted. -/
theorem free_energy_reference (G : PdelEulerian.Gas) (viscosity : ℝ) (hv : 0 ≤ viscosity)
    (x T : ℝ) (hT : 0 < T) :
    PdelBasic.freeEnergy (referenceMaterial G viscosity hv) x T =
      x^2/2 + PdelEulerian.ThermalState.freeEnergyReal G G.rhoRef T -
        G.rhoRef * G.cv * G.tempRef := by
  simp only [PdelBasic.freeEnergy, referenceMaterial,
    PdelEulerian.ThermalState.freeEnergyReal, zero_mul, sub_zero]
  rw [Real.log_div (ne_of_gt hT) (ne_of_gt G.tempRef_pos)]
  ring

theorem entropy_reference (G : PdelEulerian.Gas) (viscosity : ℝ) (hv : 0 ≤ viscosity)
    (temp entropy : PdelEulerian.Scalar) (ht : ∀ p, 0 < temp p)
    (x : ℝ) (p : PdelEulerian.ST) :
    PdelBasic.entropyState (referenceMaterial G viscosity hv) x (temp p) =
      -(referenceState G temp entropy ht).phiTemp G p := by
  simp only [PdelBasic.entropyState, referenceMaterial, referenceState,
    PdelEulerian.ThermalState.phiTemp, PdelEulerian.ThermalState.logTemp,
    PdelEulerian.ThermalState.logRho, PdelEulerian.eval_add, PdelEulerian.eval_sub,
    PdelEulerian.eval_mul, PdelEulerian.eval_neg, PdelEulerian.eval_C,
    PdelEulerian.slog_apply, zero_mul, zero_add, sub_self, mul_zero, add_zero]
  rw [Real.log_div (ne_of_gt (ht p)) (ne_of_gt G.tempRef_pos)]
  ring

theorem mixed_internal_reference (G : PdelEulerian.Gas) (viscosity : ℝ) (hv : 0 ≤ viscosity)
    (temp entropy : PdelEulerian.Scalar) (ht : ∀ p, 0 < temp p)
    (x : ℝ) (p : PdelEulerian.ST) :
    PdelBasic.mixedInternal (referenceMaterial G viscosity hv) x (temp p) (entropy p) =
      x^2/2 + (referenceState G temp entropy ht).mixedInternal G p -
        G.rhoRef * G.cv * G.tempRef := by
  rw [PdelBasic.mixedInternal, free_energy_reference G viscosity hv x (temp p) (ht p)]
  simp only [PdelEulerian.ThermalState.mixedInternal,
    PdelEulerian.ThermalState.freeEnergy, referenceState,
    PdelEulerian.ThermalState.logTemp, PdelEulerian.ThermalState.logRho,
    PdelEulerian.eval_add, PdelEulerian.eval_sub, PdelEulerian.eval_mul,
    PdelEulerian.eval_C, PdelEulerian.eval_one, PdelEulerian.slog_apply,
    PdelEulerian.ThermalState.freeEnergyReal]
  ring

/-- Both variational thermal coefficients become literally the same quantity
under this fixed-density thermal identification. -/
theorem conjugacy_residual_reference (G : PdelEulerian.Gas) (viscosity : ℝ) (hv : 0 ≤ viscosity)
    (temp entropy : PdelEulerian.Scalar) (ht : ∀ p, 0 < temp p)
    (P : PdelBasic.Path) (t : ℝ) (p : PdelEulerian.ST)
    (hT : P.theta t = temp p) (hs : P.entropy t = entropy p) :
    PdelBasic.thermalResidual (referenceMaterial G viscosity hv) P t =
      (referenceState G temp entropy ht).conjugacyResidual G p := by
  unfold PdelBasic.thermalResidual
  rw [hT, hs, entropy_reference]
  change entropy p - (-(referenceState G temp entropy ht).phiTemp G p) =
    (referenceState G temp entropy ht).phiTemp G p + entropy p
  ring

theorem bulk_dissipation_is_scalar (M : PdelBasic.Material) (K : PdelEulerian.Transport)
    (P : PdelEulerian.Fields) (p : PdelEulerian.ST) (hbulk : K.bulk p = M.viscosity) :
    P.viscousPower K p = PdelBasic.dissipation M (PdelEulerian.div P.velocity p) := by
  rw [PdelEulerian.Fields.bulk_power]
  change K.bulk p * (PdelEulerian.div P.velocity p)^2 = _
  rw [hbulk]
  unfold PdelBasic.dissipation PdelBasic.viscousForce
  ring

/-- The scalar donor test corresponds to div(xi), not to an arbitrary component
of xi. This is a bulk constitutive bridge, not an equivalence of kinematics. -/
theorem bulk_spending_is_scalar (M : PdelBasic.Material) (K : PdelEulerian.Transport)
    (P : PdelEulerian.Fields) (xi : PdelEulerian.Vector)
    (p : PdelEulerian.ST) (selector : ℝ) (hbulk : K.bulk p = M.viscosity) :
    P.viscousPower K p * selector - PdelEulerian.stressWork (P.viscousStress K) xi p =
      PdelBasic.spending M (PdelEulerian.div P.velocity p) (PdelEulerian.div xi p) selector := by
  rw [bulk_dissipation_is_scalar M K P p hbulk]
  simp [PdelBasic.spending, PdelBasic.viscousForce, PdelEulerian.stressWork,
    PdelEulerian.Fields.viscousStress, PdelEulerian.div, hbulk]
  ring

/-- A precise obstruction to identifying the whole solid free energy with
an x-independent gas at fixed density by changing only an additive datum. -/
theorem no_full_fixed_density_identification (M : PdelBasic.Material) (G : PdelEulerian.Gas)
    (rho datum : ℝ) :
    ¬ (∀ x : ℝ, PdelBasic.freeEnergy M x M.thetaRef =
      PdelEulerian.ThermalState.freeEnergyReal G rho M.thetaRef + datum) := by
  intro h
  have h0 := h 0
  have h1 := h 1
  simp only [PdelBasic.freeEnergy, sub_self, zero_mul, mul_zero, zero_pow,
    one_pow, mul_one, sub_zero, zero_add] at h0 h1
  linarith [M.stiffness_pos]

end PdelBridge
