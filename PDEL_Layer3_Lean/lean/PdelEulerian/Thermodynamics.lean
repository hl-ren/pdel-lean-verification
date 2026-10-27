import PdelEulerian.VectorCalculus

noncomputable section
namespace PdelEulerian

structure Gas where
  cv : ℝ
  gasR : ℝ
  rhoRef : ℝ
  tempRef : ℝ
  cv_pos : 0 < cv
  gasR_pos : 0 < gasR
  rhoRef_pos : 0 < rhoRef
  tempRef_pos : 0 < tempRef

/-- No balance law or conjugacy is a field of this structure. -/
structure ThermalState where
  rho : Scalar
  temp : Scalar
  entropy : Scalar
  rho_pos : ∀ p, 0 < rho p
  temp_pos : ∀ p, 0 < temp p

namespace ThermalState

def invRho (S : ThermalState) : Scalar := reciprocal S.rho (fun p => ne_of_gt (S.rho_pos p))
def invTemp (S : ThermalState) : Scalar := reciprocal S.temp (fun p => ne_of_gt (S.temp_pos p))
def logRho (G : Gas) (S : ThermalState) : Scalar :=
  slog S.rho (fun p => ne_of_gt (S.rho_pos p))-C (Real.log G.rhoRef)
def logTemp (G : Gas) (S : ThermalState) : Scalar :=
  slog S.temp (fun p => ne_of_gt (S.temp_pos p))-C (Real.log G.tempRef)

def freeEnergy (G : Gas) (S : ThermalState) : Scalar :=
  S.rho*C G.cv*S.temp*(1-logTemp G S)+S.rho*C G.gasR*S.temp*logRho G S

def phiRho (G : Gas) (S : ThermalState) : Scalar :=
  C G.cv*S.temp*(1-logTemp G S)+C G.gasR*S.temp*(logRho G S+1)

def phiTemp (G : Gas) (S : ThermalState) : Scalar :=
  -S.rho*C G.cv*logTemp G S+S.rho*C G.gasR*logRho G S

def pressure (G : Gas) (S : ThermalState) : Scalar := S.rho*phiRho G S-freeEnergy G S

def mixedInternal (G : Gas) (S : ThermalState) : Scalar := freeEnergy G S+S.temp*S.entropy

def conjugacyResidual (G : Gas) (S : ThermalState) : Scalar := phiTemp G S+S.entropy

@[simp] theorem pressure_ideal_gas (G : Gas) (S : ThermalState) :
    pressure G S = S.rho*C G.gasR*S.temp := by
  unfold pressure phiRho freeEnergy
  ring

theorem internal_energy_on_conjugacy (G : Gas) (S : ThermalState)
    {p : ST} (h : conjugacyResidual G S p=0) :
    mixedInternal G S p = S.rho p*G.cv*S.temp p := by
  simp only [conjugacyResidual, phiTemp, mixedInternal, freeEnergy,
    eval_add, eval_sub, eval_mul, eval_neg, eval_C, eval_one] at h ⊢
  linear_combination S.temp p*h

/-- An actual spatial/time chain rule for the explicit logarithmic free energy. -/
theorem d_freeEnergy (G : Gas) (S : ThermalState) (i : Fin 4) :
    d i (freeEnergy G S) = phiRho G S*d i S.rho+phiTemp G S*d i S.temp := by
  unfold freeEnergy phiRho phiTemp logRho logTemp
  simp only [d_add, d_mul, d_sub, d_C, d_one, d_slog]
  ext p
  simp only [eval_add, eval_sub, eval_mul, eval_neg, eval_C, eval_one,
    eval_zero, reciprocal_apply, slog_apply]
  field_simp [ne_of_gt (S.rho_pos p), ne_of_gt (S.temp_pos p)]
  ring

theorem d_pressure (G : Gas) (S : ThermalState) (i : Fin 4) :
    d i (pressure G S) = S.rho*d i (phiRho G S)-phiTemp G S*d i S.temp := by
  unfold pressure
  rw [d_sub, d_mul, d_freeEnergy]
  ring

/-- Conservative chain rule for a CURRENT-VOLUME energy density, off shell. -/
theorem conservative_internal_chain (G : Gas) (S : ThermalState) (v : Vector) :
    conservative v (mixedInternal G S)+pressure G S*div v =
      phiRho G S*massResidual S.rho v+
      S.temp*conservative v S.entropy+
      conjugacyResidual G S*material v S.temp := by
  simp only [conservative_split, massResidual, mixedInternal,
    conjugacyResidual, material, adv, dot, grad, dt, dx,
    d_add, d_mul, d_freeEnergy]
  unfold pressure
  ring

/-- Scalar constitutive function used in the literal parameter perturbation. -/
def freeEnergyReal (G : Gas) (rho temp : ℝ) : ℝ :=
  rho*G.cv*temp*(1-(Real.log temp-Real.log G.tempRef))+
    rho*G.gasR*temp*(Real.log rho-Real.log G.rhoRef)

/-- Genuine derivative of the two-input constitutive function along arbitrary jets. -/
theorem freeEnergyReal_hasDerivAt (G : Gas)
    {r t : ℝ → ℝ} {dr dtemp e : ℝ}
    (hr : HasDerivAt r dr e) (ht : HasDerivAt t dtemp e)
    (hr0 : 0 < r e) (ht0 : 0 < t e) :
    HasDerivAt (fun u => freeEnergyReal G (r u) (t u))
      ((G.cv*t e*(1-(Real.log (t e)-Real.log G.tempRef))+
          G.gasR*t e*(Real.log (r e)-Real.log G.rhoRef+1))*dr+
        (-r e*G.cv*(Real.log (t e)-Real.log G.tempRef)+
          r e*G.gasR*(Real.log (r e)-Real.log G.rhoRef))*dtemp) e := by
  have hlr := (hr.log (ne_of_gt hr0)).sub_const (Real.log G.rhoRef)
  have hlt := (ht.log (ne_of_gt ht0)).sub_const (Real.log G.tempRef)
  have h := (((hr.mul_const G.cv).mul ht).mul (hlt.const_sub 1)).add
    (((hr.mul_const G.gasR).mul ht).mul hlr)
  convert h using 1 <;> field_simp [ne_of_gt hr0, ne_of_gt ht0] <;> ring

/-- The conjugate coefficient is the actual partial derivative with respect to
rho of the explicit real constitutive function. -/
theorem density_partial_derivative (G : Gas) (S : ThermalState) (p : ST) :
    deriv (fun r => freeEnergyReal G r (S.temp p)) (S.rho p)=phiRho G S p := by
  have h := freeEnergyReal_hasDerivAt G (hasDerivAt_id (S.rho p))
    (hasDerivAt_const (S.rho p) (S.temp p)) (S.rho_pos p) (S.temp_pos p)
  simpa [phiRho,logTemp,logRho] using h.deriv

/-- The entropy-conjugate coefficient is an actual temperature derivative, not
a formal symbol labelled as such. -/
theorem temperature_partial_derivative (G : Gas) (S : ThermalState) (p : ST) :
    deriv (fun T => freeEnergyReal G (S.rho p) T) (S.temp p)=phiTemp G S p := by
  have h := freeEnergyReal_hasDerivAt G
    (hasDerivAt_const (S.temp p) (S.rho p)) (hasDerivAt_id (S.temp p))
    (S.rho_pos p) (S.temp_pos p)
  simpa only [phiTemp, logTemp, logRho, eval_add, eval_sub, eval_mul, eval_neg,
    eval_C, slog_apply, mul_zero, mul_one, zero_add, add_zero] using h.deriv

/-- Reference-ratio and logarithmic-difference conventions are identical. -/
theorem logarithm_reference_ratio (G : Gas) (S : ThermalState) (p : ST) :
    logTemp G S p = Real.log (S.temp p/G.tempRef) ∧
    logRho G S p = Real.log (S.rho p/G.rhoRef) := by
  constructor
  · simp [logTemp, Real.log_div (ne_of_gt (S.temp_pos p)) (ne_of_gt G.tempRef_pos)]
  · simp [logRho, Real.log_div (ne_of_gt (S.rho_pos p)) (ne_of_gt G.rhoRef_pos)]

end ThermalState
end PdelEulerian
