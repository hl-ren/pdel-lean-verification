import PdelBasic.Stationarity

/-! Off-shell energy identity, temperature equation and finite-interval budgets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace PdelBasic

def internalEnergy (M : Material) (P : Path) (t : ℝ) : ℝ :=
  mixedInternal M (P.x t) (P.theta t) (P.entropy t)

def totalEnergy (M : Material) (P : Path) (t : ℝ) : ℝ :=
  kinetic M (P.v t) + internalEnergy M P t

/-- An actual time derivative, valid even OFF the solution manifold. -/
theorem totalEnergy_off_shell (M : Material) (P : Path) (L : Loads) (t : ℝ) :
    HasDerivAt (totalEnergy M P)
      (P.v t * mechanicalResidual M P L t +
       deriv P.theta t * thermalResidual M P t + entropyResidual M P L t +
       L.force t * P.v t - L.heatOut t) t := by
  have hi := mixedInternal_chain_rule M (P.dx t) (path_theta_hasDerivAt P t)
    (path_entropy_hasDerivAt P t) (P.theta_pos t)
  have hk := kinetic_hasDerivAt M (P.dv t)
  convert hk.add hi using 1 <;>
    dsimp [totalEnergy, internalEnergy, mechanicalResidual, thermalResidual,
      entropyResidual, dissipation, viscousForce] <;> ring

/-- Energy conservation is a consequence of mixed stationarity. -/
theorem energy_from_stationarity (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivAt (totalEnergy M P) (L.force t * P.v t - L.heatOut t) t := by
  obtain ⟨hm, hT, hs⟩ := (stationary_iff_residuals M P L hab).mp hst t ht
  simpa only [hm, hT, hs, mul_zero, zero_add, add_zero] using totalEnergy_off_shell M P L t

theorem finite_interval_energy_balance (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b) :
    totalEnergy M P b - totalEnergy M P a =
      ∫ t in a..b, L.force t * P.v t - L.heatOut t := by
  have hcont := (L.force_c1.continuous.mul P.v_c1.continuous).sub L.heatOut_cont
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => energy_from_stationarity M P L hab hst
      (by simpa only [uIcc_of_le hab.le] using ht))
    (hcont.intervalIntegrable a b)

theorem internalEnergy_from_stationarity (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivAt (internalEnergy M P)
      (elasticForce M (P.x t) (P.theta t) * P.v t +
        dissipation M (P.v t) - L.heatOut t) t := by
  obtain ⟨_, hconj, hheat⟩ := (pdel_basic_variational_theorem M P L hab).mp hst t ht
  have hi := mixedInternal_chain_rule M (P.dx t) (path_theta_hasDerivAt P t)
    (path_entropy_hasDerivAt P t) (P.theta_pos t)
  have heq : elasticForce M (P.x t) (P.theta t) * P.v t +
      (P.entropy t - entropyState M (P.x t) (P.theta t)) * deriv P.theta t +
      P.theta t * deriv P.entropy t =
      elasticForce M (P.x t) (P.theta t) * P.v t +
        dissipation M (P.v t) - L.heatOut t := by
    rw [hconj]
    nlinarith [hheat]
  rw [heq] at hi
  exact hi

/-- The same Hd in the action supplies the internal energy increase. -/
theorem internal_history_budget (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b) :
    internalEnergy M P b - internalEnergy M P a =
      (∫ t in a..b, elasticForce M (P.x t) (P.theta t) * P.v t) +
      powerHistory (fun t => dissipation M (P.v t)) a b -
      powerHistory L.heatOut a b := by
  have hx := P.x_c1.continuous
  have hT := P.theta_c1.continuous
  have hv := P.v_c1.continuous
  have hel : Continuous (fun t => elasticForce M (P.x t) (P.theta t) * P.v t) := by
    dsimp [elasticForce]
    fun_prop
  have hdis := path_dissipation_continuous M P
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => internalEnergy_from_stationarity M P L hab hst
      (by simpa only [uIcc_of_le hab.le] using ht))
    (((hel.add hdis).sub L.heatOut_cont).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub ((hel.add hdis).intervalIntegrable a b)
        (L.heatOut_cont.intervalIntegrable a b),
      intervalIntegral.integral_add (hel.intervalIntegrable a b)
        (hdis.intervalIntegrable a b)] at hI
  exact hI.symm

/-- Differentiate the derived conjugacy on an open neighborhood, not at one isolated point. -/
theorem temperature_equation_from_stationarity (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    M.capacity * deriv P.theta t + M.beta * P.theta t * P.v t + L.heatOut t =
      dissipation M (P.v t) := by
  have heqs := (pdel_basic_variational_theorem M P L hab).mp hst
  have hevent : P.entropy =ᶠ[𝓝 t]
      (fun u => entropyState M (P.x u) (P.theta u)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact (heqs u ⟨hu.1.le, hu.2.le⟩).2.1
  have hsd := (entropyState_hasDerivAt M (P.dx t) (path_theta_hasDerivAt P t)
    (P.theta_pos t)).congr_of_eventuallyEq hevent
  have hheat := (heqs t ⟨ht.1.le, ht.2.le⟩).2.2
  rw [hsd.deriv] at hheat
  have halg : P.theta t * (M.beta * P.v t + M.capacity * deriv P.theta t / P.theta t) +
      L.heatOut t = M.capacity * deriv P.theta t +
        M.beta * P.theta t * P.v t + L.heatOut t := by
    field_simp [ne_of_gt (P.theta_pos t)] <;> ring
  rw [halg] at hheat
  exact hheat

theorem entropy_flux_identity (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    deriv P.entropy t + L.heatOut t / P.theta t =
      dissipation M (P.v t) / P.theta t := by
  have hs := ((pdel_basic_variational_theorem M P L hab).mp hst t ht).2.2
  apply (eq_div_iff (ne_of_gt (P.theta_pos t))).mpr
  field_simp [ne_of_gt (P.theta_pos t)]
  nlinarith [hs]

theorem entropy_production_nonnegative (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ deriv P.entropy t + L.heatOut t / P.theta t := by
  rw [entropy_flux_identity M P L hab hst ht]
  exact div_nonneg (dissipation_nonnegative M (P.v t)) (P.theta_pos t).le

/-- Positive viscosity produces nonnegative entropy in an adiabatic specimen. -/
theorem adiabatic_entropy_nonnegative (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Icc a b) (hq : L.heatOut t = 0) :
    0 ≤ deriv P.entropy t := by
  simpa only [hq, zero_div, add_zero] using
    entropy_production_nonnegative M P L hab hst ht

/-- If both ports vanish, the actual derivative of stored plus kinetic energy vanishes. -/
theorem closed_energy_derivative_zero (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Icc a b) (hf : L.force t = 0) (hq : L.heatOut t = 0) :
    HasDerivAt (totalEnergy M P) 0 t := by
  simpa only [hf, hq, zero_mul, sub_zero] using energy_from_stationarity M P L hab hst ht

/-- For Newton cooling, account also for the heat bath's entropy input. -/
theorem reservoir_entropy_identity (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t bath conductance : ℝ} (ht : t ∈ Icc a b) (hb : 0 < bath)
    (hq : L.heatOut t = conductance * (P.theta t - bath)) :
    deriv P.entropy t + L.heatOut t / bath =
      dissipation M (P.v t) / P.theta t +
        conductance * (P.theta t - bath)^2 / (P.theta t * bath) := by
  have hs := entropy_flux_identity M P L hab hst ht
  calc
    _ = (deriv P.entropy t + L.heatOut t / P.theta t) +
        L.heatOut t * (1 / bath - 1 / P.theta t) := by
      field_simp [ne_of_gt (P.theta_pos t), ne_of_gt hb] <;> ring
    _ = _ := by
      rw [hs, hq]
      field_simp [ne_of_gt (P.theta_pos t), ne_of_gt hb] <;> ring

theorem reservoir_entropy_nonnegative (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t bath conductance : ℝ} (ht : t ∈ Icc a b) (hb : 0 < bath)
    (hc : 0 ≤ conductance)
    (hq : L.heatOut t = conductance * (P.theta t - bath)) :
    0 ≤ deriv P.entropy t + L.heatOut t / bath := by
  rw [reservoir_entropy_identity M P L hab hst ht hb hq]
  exact add_nonneg
    (div_nonneg (dissipation_nonnegative M (P.v t)) (P.theta_pos t).le)
    (div_nonneg (mul_nonneg hc (sq_nonneg _)) (mul_pos (P.theta_pos t) hb).le)

/-- A single theorem exposes the variational-to-dynamical-to-energetic chain. -/
theorem basic_variation_and_energy (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b) :
    GoverningOn M P L a b ∧
    (∀ t ∈ Icc a b,
      HasDerivAt (totalEnergy M P) (L.force t * P.v t - L.heatOut t) t) ∧
    (totalEnergy M P b - totalEnergy M P a =
      ∫ t in a..b, L.force t * P.v t - L.heatOut t) := by
  exact ⟨(pdel_basic_variational_theorem M P L hab).mp hst,
    (fun _ ht => energy_from_stationarity M P L hab hst ht),
    finite_interval_energy_balance M P L hab hst⟩

end PdelBasic
