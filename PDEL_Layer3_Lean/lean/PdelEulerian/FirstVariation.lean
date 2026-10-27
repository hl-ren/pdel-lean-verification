import PdelEulerian.History

noncomputable section
namespace PdelEulerian

/-- Independent smooth directions. Boundary admissibility is imposed later,
    not by replacing a displacement with a velocity projection. -/
structure Test where
  xi : Vector
  a : Vector
  temperature : Scalar
  entropySelector : Scalar

namespace Test

def drho (P : Fields) (V : Test) : Scalar := densityVariation P.state.rho V.xi
def dv (P : Fields) (V : Test) : Vector := velocityVariation P.velocity V.xi
def dtemp (P : Fields) (V : Test) : Scalar :=
  scalarVariation P.state.temp V.xi+V.temperature

def ds (P : Fields) (V : Test) : Scalar :=
  densityVariation P.state.entropy V.xi+
    conservative P.velocity P.state.entropy*V.entropySelector

def dmagnetic (V : Test) : Vector := curl V.a

def zero : Test := ⟨0,0,0,0⟩

end Test

/-- A literal finite jet implementing the source's PDEL mixed operation.
    Past source integrands and current resistive/viscous coforces are LOCKED.
    The explicit linear weak-donor term is part of the declared PDEL operation;
    it is not inferred from the fundamental theorem of calculus. -/
def mixedDensity (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) (e : ℝ) (p : ST) : ℝ :=
  let rr := P.state.rho p+e*(V.drho P p)
  let tt := P.state.temp p+e*(V.dtemp P p)
  let ss := P.state.entropy p+e*(V.ds P p)
  let vv : Fin 3 → ℝ := fun i => P.velocity i p+e*(V.dv P i p)
  let bb : Fin 3 → ℝ := fun i => P.magnetic i p+e*(V.dmagnetic i p)
  let upper := p 0+e*V.entropySelector p
  rr/2*rdot vv vv-ThermalState.freeEnergyReal G rr tt-tt*ss-rdot bb bb/2
    -F.receiverHistory (div (P.heatFlux K)) t0 p upper
    +F.receiverHistory (P.joulePower K) t0 p upper
    +F.receiverHistory (P.viscousPower K) t0 p upper
    -e*(dot (P.resistance K) (V.a-cross V.xi P.magnetic) p+
         stressWork (P.viscousStress K) V.xi p)

/-- The unperturbed state-history density, not a residual functional. -/
def stateHistoryDensity (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (p : ST) : ℝ :=
  P.kinetic p-P.state.freeEnergy G p-P.state.temp p*P.state.entropy p-
    normSq P.magnetic p/2-
    F.currentHistory (div (P.heatFlux K)) t0 p+
    F.currentHistory (P.joulePower K) t0 p+
    F.currentHistory (P.viscousPower K) t0 p

/-- First variation before integration by parts; this formula is obtained by
    differentiating mixedDensity in mixedDensity_hasDerivAt. -/
def rawVariation (G : Gas) (K : Transport) (P : Fields) (V : Test) : Scalar :=
  P.state.rho*dot P.velocity (V.dv P)+C (1/2)*normSq P.velocity*(V.drho P)
  -P.state.phiRho G*(V.drho P)
  -(P.state.phiTemp G+P.state.entropy)*(V.dtemp P)
  -P.state.temp*(V.ds P)-dot P.magnetic V.dmagnetic
  +(P.joulePower K+P.viscousPower K-div (P.heatFlux K))*V.entropySelector
  -dot (P.resistance K) (V.a-cross V.xi P.magnetic)
  -stressWork (P.viscousStress K) V.xi

theorem mixedDensity_at_zero (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) (p : ST) :
    mixedDensity G K P F t0 V 0 p=stateHistoryDensity G K P F t0 p := by
  simp only [mixedDensity, stateHistoryDensity, Fields.kinetic, normSq, dot,
    rdot, ThermalState.freeEnergyReal, ThermalState.freeEnergy,
    ThermalState.logRho, ThermalState.logTemp,
    MaterialChart.receiver_at_current, zero_mul, add_zero, sub_zero,
    eval_mul, eval_add, eval_sub, eval_C, eval_one, slog_apply]
  ring

/-- The magnetic jet is the curl of the independent potential jet. -/
theorem varied_magnetic_is_curl (P : Fields) (V : Test) (e : ℝ) :
    curl (P.potential+scale (C e) V.a)=P.magnetic+scale (C e) V.dmagnetic := by
  rw [curl_add, curl_C_scale]
  rfl

theorem affine_jet_hasDerivAt (a da : ℝ) :
    HasDerivAt (fun e : ℝ => a+e*da) da 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const da).const_add a

theorem norm_jet_hasDerivAt (v dv : Fin 3 → ℝ) :
    HasDerivAt (fun e : ℝ => rdot (fun i => v i+e*dv i) (fun i => v i+e*dv i))
      (2*rdot v dv) 0 := by
  have h0 := (affine_jet_hasDerivAt (v 0) (dv 0)).pow 2
  have h1 := (affine_jet_hasDerivAt (v 1) (dv 1)).pow 2
  have h2 := (affine_jet_hasDerivAt (v 2) (dv 2)).pow 2
  convert (h0.add h1).add h2 using 1 <;> simp [rdot, pow_two] <;> ring

/-- Actual real parameter derivative of ALL storage terms and literal endpoint
    histories. No governing equation, mass equation, or conjugacy is used. -/
theorem mixedDensity_hasDerivAt (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) (p : ST) :
    HasDerivAt (fun e => mixedDensity G K P F t0 V e p) (rawVariation G K P V p) 0 := by
  have hr := affine_jet_hasDerivAt (P.state.rho p) (V.drho P p)
  have ht := affine_jet_hasDerivAt (P.state.temp p) (V.dtemp P p)
  have hs := affine_jet_hasDerivAt (P.state.entropy p) (V.ds P p)
  have hv := norm_jet_hasDerivAt (valueV P.velocity p) (valueV (V.dv P) p)
  have hb := norm_jet_hasDerivAt (valueV P.magnetic p) (valueV V.dmagnetic p)
  have hf := ThermalState.freeEnergyReal_hasDerivAt G hr ht
    (by simpa using P.state.rho_pos p) (by simpa using P.state.temp_pos p)
  have hq := F.receiver_endpoint_derivative (div (P.heatFlux K)) t0 p (V.entropySelector p)
  have hj := F.receiver_endpoint_derivative (P.joulePower K) t0 p (V.entropySelector p)
  have hn := F.receiver_endpoint_derivative (P.viscousPower K) t0 p (V.entropySelector p)
  have hw := (hasDerivAt_id (0 : ℝ)).mul_const
    (dot (P.resistance K) (V.a-cross V.xi P.magnetic) p+
      stressWork (P.viscousStress K) V.xi p)
  have h := (((((((hr.div_const 2).mul hv).sub hf).sub (ht.mul hs)).sub
    (hb.div_const 2)).sub hq).add hj).add hn
  convert h.sub hw using 1
  simp only [rawVariation, ThermalState.phiRho, ThermalState.phiTemp,
    ThermalState.logRho, ThermalState.logTemp, dot, rdot, valueV, normSq,
    eval_mul, eval_add, eval_sub, eval_neg, eval_C, eval_one, slog_apply,
    zero_mul, add_zero, one_mul]
  ring

theorem actual_local_first_variation (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) (p : ST) :
    deriv (fun e => mixedDensity G K P F t0 V e p) 0=rawVariation G K P V p :=
  (mixedDensity_hasDerivAt G K P F t0 V p).deriv

/-- Resistive donor calibration uses two independent jets before evaluation.
    A spatially varying selector is harmless here because this pairing has no
    derivative of either weak test. This is not true of grad(v*selector). -/
theorem resistive_power_calibration (K : Transport) (P : Fields) (c : Scalar) :
    dot (P.resistance K)
      (scale c (dtV P.potential)-cross (scale c P.velocity) P.magnetic)=
      P.joulePower K*c := by
  simp [dot, cross, scale, Fields.joulePower, Fields.relativeRate] <;> ring

theorem kinetic_weak_identity (P : Fields) (xi : Vector) :
    P.state.rho*dot P.velocity (velocityVariation P.velocity xi)+
      C (1/2)*normSq P.velocity*densityVariation P.state.rho xi =
    -dot (conservativeMomentum P.state.rho P.velocity) xi+
      dt (P.state.rho*dot P.velocity xi)+
      div (scale (P.state.rho*dot P.velocity xi) P.velocity-scale P.kinetic xi) := by
  simp only [velocityVariation, densityVariation, conservativeMomentum,
    Fields.kinetic, normSq, dot, dtV, advV, adv, grad, div, scale,
    dt, dx, Pi.add_apply, Pi.sub_apply, d_add, d_sub, d_mul, d_C]
  ext p
  simp only [eval_add,eval_sub,eval_mul,eval_neg,eval_zero,eval_one,eval_C,eval_pow]
  ring

theorem thermal_state_weak_identity (G : Gas) (P : Fields) (xi : Vector) :
    -P.state.phiRho G*densityVariation P.state.rho xi-
      (P.state.phiTemp G+P.state.entropy)*scalarVariation P.state.temp xi-
      P.state.temp*densityVariation P.state.entropy xi =
    -dot (grad (P.state.pressure G)) xi+
      div (scale (P.state.mixedInternal G+P.state.pressure G) xi) := by
  have hsum : P.state.mixedInternal G+P.state.pressure G=
      P.state.rho*P.state.phiRho G+P.state.temp*P.state.entropy := by
    unfold ThermalState.mixedInternal ThermalState.pressure
    ring
  rw [hsum]
  simp only [densityVariation, scalarVariation, dot, adv, grad, div, scale,
    dx, d_add, d_mul, ThermalState.d_pressure]
  ring

/-- The complete boundary current obtained from the pointwise first variation. -/
def variationCurrent (G : Gas) (K : Transport) (P : Fields) (V : Test) : Vector4 :=
  spacetimeCurrent (P.state.rho*dot P.velocity V.xi)
    (scale (P.state.rho*dot P.velocity V.xi) P.velocity+
      scale (P.state.mixedInternal G+P.state.pressure G-P.kinetic) V.xi-
      matvec (transpose (P.viscousStress K)) V.xi-cross V.a P.magnetic)

def residualPairing (G : Gas) (K : Transport) (P : Fields) (V : Test) : Scalar :=
  dot (P.momentumResidual G K) V.xi+dot (P.ohmResidual K) V.a+
    P.thermalResidual G*V.temperature+P.entropyResidual K*V.entropySelector

/-- Local integration-by-parts identity, valid even OFF the mass manifold.
    Every derivative is an actual Cartesian derivative. -/
theorem first_variation_divergence_identity (G : Gas) (K : Transport) (P : Fields) (V : Test) :
    rawVariation G K P V = -residualPairing G K P V+div4 (variationCurrent G K P V) := by
  have hk := kinetic_weak_identity P V.xi
  have ht := thermal_state_weak_identity G P V.xi
  have hb := magnetic_weak_identity P.magnetic V.a
  have hn := stress_weak_identity (P.viscousStress K) V.xi
  unfold rawVariation residualPairing variationCurrent
  simp only [Test.drho, Test.dv, Test.dtemp, Test.ds, Test.dmagnetic,
    Fields.momentumResidual, Fields.ohmResidual, Fields.thermalResidual,
    Fields.entropyResidual, Fields.current, ThermalState.conjugacyResidual, div4_current]
  simp only [div, scale, matvec, transpose, dt, dx,
    Pi.add_apply, Pi.sub_apply, d_add, d_sub, d_mul, d_C] at hk ht hb hn ⊢
  simp only [dot, cross, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Pi.add_apply, Pi.sub_apply] at hk ht hb hn ⊢
  linear_combination hk+ht+hb+hn

end PdelEulerian
