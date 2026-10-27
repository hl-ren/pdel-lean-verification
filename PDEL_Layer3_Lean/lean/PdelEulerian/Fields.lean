import PdelEulerian.Thermodynamics

noncomputable section
namespace PdelEulerian

/-- Smooth, symmetric positive-definite resistivity with its smooth inverse.
    These are constitutive properties, NOT equations of motion or Ohm's law. -/
structure Transport where
  eta : Tensor
  sigma : Tensor
  inverse : ∀ i j,
    eta i 0*sigma 0 j+eta i 1*sigma 1 j+eta i 2*sigma 2 j = if i=j then 1 else 0
  eta_symmetric : ∀ i j, eta i j=eta j i
  sigma_symmetric : ∀ i j, sigma i j=sigma j i
  eta_pos : ∀ (p : ST) (z : Fin 3 → ℝ), z ≠ 0 →
    0 < rdot z (fun i => eta i 0 p*z 0+eta i 1 p*z 1+eta i 2 p*z 2)
  sigma_nonneg : ∀ (p : ST) (z : Fin 3 → ℝ),
    0 ≤ rdot z (fun i => sigma i 0 p*z 0+sigma i 1 p*z 1+sigma i 2 p*z 2)
  bulk : Scalar
  thermal : Scalar
  bulk_nonneg : ∀ p, 0 ≤ bulk p
  thermal_nonneg : ∀ p, 0 ≤ thermal p

/-- No momentum, induction, thermal, or energy equation occurs here. -/
structure Fields where
  state : ThermalState
  velocity : Vector
  potential : Vector

namespace Transport

theorem eta_sigma (K : Transport) (w : Vector) : matvec K.eta (matvec K.sigma w)=w := by
  funext i
  change K.eta i 0*(K.sigma 0 0*w 0+K.sigma 0 1*w 1+K.sigma 0 2*w 2)+
    K.eta i 1*(K.sigma 1 0*w 0+K.sigma 1 1*w 1+K.sigma 1 2*w 2)+
    K.eta i 2*(K.sigma 2 0*w 0+K.sigma 2 1*w 1+K.sigma 2 2*w 2)=w i
  calc
    _ = (K.eta i 0*K.sigma 0 0+K.eta i 1*K.sigma 1 0+K.eta i 2*K.sigma 2 0)*w 0+
        (K.eta i 0*K.sigma 0 1+K.eta i 1*K.sigma 1 1+K.eta i 2*K.sigma 2 1)*w 1+
        (K.eta i 0*K.sigma 0 2+K.eta i 1*K.sigma 1 2+K.eta i 2*K.sigma 2 2)*w 2 := by ring
    _ = _ := by
      rw [K.inverse, K.inverse, K.inverse]
      fin_cases i <;> simp

/-- The reverse inverse follows by symmetry; no independent Ohm equation is used. -/
theorem sigma_eta (K : Transport) (w : Vector) : matvec K.sigma (matvec K.eta w)=w := by
  have hinv : ∀ i j,
      K.sigma i 0*K.eta 0 j+K.sigma i 1*K.eta 1 j+K.sigma i 2*K.eta 2 j=
      if i=j then 1 else 0 := by
    intro i j
    have h := K.inverse j i
    simpa only [K.sigma_symmetric, K.eta_symmetric, mul_comm, eq_comm] using h
  funext i
  change K.sigma i 0*(K.eta 0 0*w 0+K.eta 0 1*w 1+K.eta 0 2*w 2)+
    K.sigma i 1*(K.eta 1 0*w 0+K.eta 1 1*w 1+K.eta 1 2*w 2)+
    K.sigma i 2*(K.eta 2 0*w 0+K.eta 2 1*w 1+K.eta 2 2*w 2)=w i
  calc
    _ = (K.sigma i 0*K.eta 0 0+K.sigma i 1*K.eta 1 0+K.sigma i 2*K.eta 2 0)*w 0+
        (K.sigma i 0*K.eta 0 1+K.sigma i 1*K.eta 1 1+K.sigma i 2*K.eta 2 1)*w 1+
        (K.sigma i 0*K.eta 0 2+K.sigma i 1*K.eta 1 2+K.sigma i 2*K.eta 2 2)*w 2 := by ring
    _ = _ := by
      rw [hinv, hinv, hinv]
      fin_cases i <;> simp

end Transport

namespace Fields

def magnetic (P : Fields) : Vector := curl P.potential
def current (P : Fields) : Vector := curl P.magnetic
def electric (P : Fields) : Vector := -dtV P.potential
def relativeRate (P : Fields) : Vector := dtV P.potential-cross P.velocity P.magnetic

def resistance (K : Transport) (P : Fields) : Vector := matvec K.sigma P.relativeRate
def joulePower (K : Transport) (P : Fields) : Scalar := dot P.relativeRate (P.resistance K)

def viscousStress (K : Transport) (P : Fields) : Tensor := fun i j =>
  if i=j then K.bulk*div P.velocity else 0

def viscousPower (K : Transport) (P : Fields) : Scalar := stressWork (P.viscousStress K) P.velocity

def heatFlux (K : Transport) (P : Fields) : Vector := -scale K.thermal (grad P.state.temp)

def kinetic (P : Fields) : Scalar := C (1/2)*P.state.rho*normSq P.velocity

def densityResidual (P : Fields) : Scalar := massResidual P.state.rho P.velocity

def momentumResidual (G : Gas) (K : Transport) (P : Fields) : Vector :=
  conservativeMomentum P.state.rho P.velocity+grad (P.state.pressure G)-
    divTensor (P.viscousStress K)-cross P.magnetic (P.resistance K)

def ohmResidual (K : Transport) (P : Fields) : Vector := P.current+P.resistance K

def thermalResidual (G : Gas) (P : Fields) : Scalar := P.state.conjugacyResidual G

def entropyResidual (K : Transport) (P : Fields) : Scalar :=
  P.state.temp*conservative P.velocity P.state.entropy+
    div (P.heatFlux K)-P.joulePower K-P.viscousPower K

theorem magnetic_divergence (P : Fields) : div P.magnetic=0 := div_curl _

theorem faraday_identity (P : Fields) : dtV P.magnetic+curl P.electric=0 := by
  rw [magnetic, electric, dt_curl, curl_neg]
  simp

theorem relative_electric_identity (P : Fields) :
    P.electric+cross P.velocity P.magnetic = -P.relativeRate := by
  funext i
  simp [electric, relativeRate]
  ring

theorem bulk_power (K : Transport) (P : Fields) :
    P.viscousPower K=K.bulk*(div P.velocity)^2 := by
  simp [viscousPower, viscousStress, stressWork, div]
  ring

theorem joule_nonnegative (K : Transport) (P : Fields) (p : ST) :
    0 ≤ P.joulePower K p := by
  exact K.sigma_nonneg p (valueV P.relativeRate p)

theorem viscous_nonnegative (K : Transport) (P : Fields) (p : ST) :
    0 ≤ P.viscousPower K p := by
  rw [bulk_power]
  exact mul_nonneg (K.bulk_nonneg p) (sq_nonneg _)

/-- Pointwise full vector Ohm equation, obtained from an independent vector residual. -/
theorem ohm_from_residual (K : Transport) (P : Fields) {p : ST}
    (h : ∀ i, P.ohmResidual K i p=0) :
    ∀ i, (P.electric+cross P.velocity P.magnetic) i p=matvec K.eta P.current i p := by
  have hr : ∀ i, P.resistance K i p = -P.current i p := by
    intro i
    have hi := h i
    change P.current i p+P.resistance K i p=0 at hi
    linarith
  have hi := congrArg (fun w : Vector => valueV w p) (K.eta_sigma P.relativeRate)
  intro i
  have hri := congrArg (fun w : Fin 3 → ℝ => w i) hi
  change (matvec K.eta (P.resistance K)) i p=P.relativeRate i p at hri
  rw [relative_electric_identity]
  simp only [matvec, eval_add, eval_mul, hr, Pi.neg_apply, eval_neg] at hri ⊢
  linarith

theorem joule_on_ohm (K : Transport) (P : Fields) {p : ST}
    (h : ∀ i, P.ohmResidual K i p=0) :
    P.joulePower K p = dot P.current (matvec K.eta P.current) p := by
  have hr : ∀ i, P.resistance K i p = -P.current i p := by
    intro i
    have hi := h i
    change P.current i p+P.resistance K i p=0 at hi
    linarith
  have he := ohm_from_residual K P h
  have he' : ∀ i, P.relativeRate i p = -(matvec K.eta P.current) i p := by
    intro i
    have hi := he i
    rw [relative_electric_identity] at hi
    simpa only [Pi.neg_apply, eval_neg, neg_eq_iff_eq_neg] using hi
  simp only [joulePower, dot, eval_add, eval_mul, he', hr]
  ring

end Fields
end PdelEulerian
