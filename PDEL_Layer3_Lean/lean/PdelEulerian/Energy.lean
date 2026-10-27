import PdelEulerian.Equations

/-!
# Energy, temperature, entropy, and actual boundary budgets

The off-shell identity exposes all four variational coefficients and the mass
residual. It is established before imposing any balance equation.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace PdelEulerian

namespace Fields

def magneticEnergy (P : Fields) : Scalar := C (1/2)*normSq P.magnetic

def totalEnergy (G : Gas) (P : Fields) : Scalar :=
  P.kinetic+P.state.mixedInternal G+P.magneticEnergy

def totalEnergyFlux (G : Gas) (K : Transport) (P : Fields) : Vector :=
  scale (P.kinetic+P.state.mixedInternal G+P.state.pressure G) P.velocity-
    matvec (transpose (P.viscousStress K)) P.velocity+
    cross P.electric P.magnetic+P.heatFlux K

def energyResidual (G : Gas) (K : Transport) (P : Fields) : Scalar :=
  dt (P.totalEnergy G)+div (P.totalEnergyFlux G K)

def temperatureResidual (G : Gas) (K : Transport) (P : Fields) : Scalar :=
  P.state.rho*C G.cv*material P.velocity P.state.temp+
    P.state.pressure G*div P.velocity+div (P.heatFlux K)-
    P.joulePower K-P.viscousPower K

def entropyFlux (K : Transport) (P : Fields) : Vector :=
  scale P.state.invTemp (P.heatFlux K)

def entropyProduction (K : Transport) (P : Fields) : Scalar :=
  P.state.invTemp*(P.joulePower K+P.viscousPower K)+
    K.thermal*P.state.invTemp^2*normSq (grad P.state.temp)

theorem magnetic_energy_kinematic (P : Fields) :
    dt P.magneticEnergy+div (cross P.electric P.magnetic)=-dot P.electric P.current := by
  have hp := poynting_product_rule P.electric P.magnetic
  have hf := P.faraday_identity
  have h0 := congrArg (fun v : Vector => v 0) hf
  have h1 := congrArg (fun v : Vector => v 1) hf
  have h2 := congrArg (fun v : Vector => v 2) hf
  simp only [magneticEnergy, normSq, dot, dt, dtV, d_add, d_mul, d_C,
    Pi.add_apply, Pi.zero_apply] at h0 h1 h2 ⊢
  ext p
  have hp' := congrArg (fun s : Scalar => s p) hp
  have h0' := congrArg (fun s : Scalar => s p) h0
  have h1' := congrArg (fun s : Scalar => s p) h1
  have h2' := congrArg (fun s : Scalar => s p) h2
  simp only [eval_add, eval_mul, eval_C, eval_neg, eval_zero, eval_sub,
    dot, current] at hp' h0' h1' h2' ⊢
  linear_combination hp'+P.magnetic 0 p*h0'+P.magnetic 1 p*h1'+P.magnetic 2 p*h2'

/-- The same relative coforce transfers signed Lorentz power and irreversible
heat. This cancellation is essential; Joule heating is not counted twice. -/
theorem resistive_energy_recombination (K : Transport) (P : Fields) :
    dot P.velocity (cross P.magnetic (P.resistance K))+P.joulePower K=
      -dot P.electric (P.resistance K) := by
  simp only [dot,cross,joulePower,relativeRate,electric,Pi.sub_apply,Pi.neg_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  ring

/-- Complete Eulerian off-shell energy identity. In particular the electric
residual has coefficient -E, and the mass residual cannot be silently discarded. -/
theorem total_energy_off_shell (G : Gas) (K : Transport) (P : Fields) :
    P.energyResidual G K =
      dot P.velocity (P.momentumResidual G K)+
      (P.state.phiRho G-C (1/2)*normSq P.velocity)*P.densityResidual+
      P.entropyResidual K+P.thermalResidual G*material P.velocity P.state.temp-
      dot P.electric (P.ohmResidual K) := by
  have hk := material_divergence_kinetic P.state.rho P.velocity
  have hu := ThermalState.conservative_internal_chain G P.state P.velocity
  have hb := P.magnetic_energy_kinematic
  have hn := stress_weak_identity (P.viscousStress K) P.velocity
  have hr := P.resistive_energy_recombination K
  unfold energyResidual totalEnergy totalEnergyFlux momentumResidual densityResidual
    entropyResidual thermalResidual ohmResidual
  simp only [div,scale,matvec,transpose,dt,dx,Pi.add_apply,Pi.sub_apply,
    d_add,d_sub,d_mul,d_C,conservative,kinetic,viscousPower,
    dot,normSq,cross,grad,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      at hk hu hb hn hr ⊢
  linear_combination hk+hu+hb-hn+hr

/-- Exact mixed-state decomposition, prior to thermal stationarity. -/
theorem mixed_internal_decomposition (G : Gas) (P : Fields) :
    P.state.mixedInternal G = P.state.rho*C G.cv*P.state.temp+
      P.state.temp*P.thermalResidual G := by
  unfold ThermalState.mixedInternal ThermalState.freeEnergy thermalResidual
    ThermalState.conjugacyResidual ThermalState.phiTemp
  ring

/-- Temperature equation follows from entropy conjugacy on a neighborhood.
This identity makes the derivative of the conjugacy residual explicit. -/
theorem temperature_residual_identity (G : Gas) (K : Transport) (P : Fields) :
    P.temperatureResidual G K = P.entropyResidual K+
      (P.state.phiRho G-C G.cv*P.state.temp)*P.densityResidual-
      P.state.temp*conservative P.velocity (P.thermalResidual G) := by
  have hu := ThermalState.conservative_internal_chain G P.state P.velocity
  rw [P.mixed_internal_decomposition G] at hu
  unfold temperatureResidual entropyResidual densityResidual
  simp only [conservative_split,material,adv,dot,grad,dt,dx,d_add,d_mul,d_C,
    massResidual,thermalResidual] at hu ⊢
  ring_nf at hu ⊢
  linear_combination hu

/-- Fourier entropy-flux identity; the heat divergence itself is not a local
production. The off-shell entropy residual remains visible. -/
theorem entropy_identity_off_shell (K : Transport) (P : Fields) :
    conservative P.velocity P.state.entropy+div (P.entropyFlux K) =
      P.state.invTemp*P.entropyResidual K+P.entropyProduction K := by
  simp only [entropyFlux,entropyProduction,entropyResidual,heatFlux,
    div,scale,grad,dx,Pi.neg_apply,d_add,d_mul,d_neg,
    ThermalState.invTemp,d_reciprocal,normSq,dot]
  ext p
  simp only [eval_add,eval_sub,eval_neg,eval_mul,eval_pow,eval_C,eval_zero,
    reciprocal_apply]
  field_simp [ne_of_gt (P.state.temp_pos p)]
  ring

theorem entropy_production_nonnegative (K : Transport) (P : Fields) (p : ST) :
    0 ≤ P.entropyProduction K p := by
  have ht : 0 ≤ P.state.invTemp p := by
    exact inv_nonneg.mpr (P.state.temp_pos p).le
  have hd : 0 ≤ P.joulePower K p+P.viscousPower K p :=
    add_nonneg (P.joule_nonnegative K p) (P.viscous_nonnegative K p)
  exact add_nonneg (mul_nonneg ht hd)
    (mul_nonneg (mul_nonneg (K.thermal_nonneg p) (sq_nonneg _))
      (normSq_nonnegative _ p))

end Fields

/-- Local total energy conservation is a consequence of the variational theorem
and mass admissibility, not an extra path field or an assumed law. -/
theorem energy_from_stationarity
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hmass : MassAdmissible Q P) (hs : Stationary Q G K P F t0) :
    ∀ p ∈ Q.closed, P.energyResidual G K p=0 := by
  have h := (eulerian_pdel_variational_theorem Q G K P F t0).mp hs
  intro p hp
  rcases h p hp with ⟨hm,hA,hT,hS⟩
  rw [P.total_energy_off_shell G K]
  simp [dot,hm,hA,hT,hS,hmass p hp]

/-- Genuine differentiation of conjugacy is used only in the open spacetime box. -/
theorem temperature_from_stationarity
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hmass : MassAdmissible Q P) (hs : Stationary Q G K P F t0)
    {p : ST} (hp : p ∈ Q.interior) : P.temperatureResidual G K p=0 := by
  have h := (eulerian_pdel_variational_theorem Q G K P F t0).mp hs
  have hclosed := Q.interior_subset hp
  rcases h p hclosed with ⟨hm,hA,hT,hS⟩
  have hd : ∀ i, d i (P.thermalResidual G) p=0 := by
    intro i
    exact d_eq_zero_on_open Q.interior_open (P.thermalResidual G)
      (fun q hq => (h q (Q.interior_subset hq)).2.2.1) hp i
  rw [P.temperature_residual_identity G K,conservative_split]
  simp only [material,adv,dot,grad,dt,dx,eval_add,eval_sub,eval_mul,
    eval_zero,hd,hT,hS,hmass p hclosed,zero_add,add_zero,zero_mul,mul_zero,sub_zero]

theorem entropy_from_stationarity
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hs : Stationary Q G K P F t0) {p : ST} (hp : p ∈ Q.closed) :
    conservative P.velocity P.state.entropy p+div (P.entropyFlux K) p =
      P.entropyProduction K p ∧ 0 ≤ P.entropyProduction K p := by
  have he := ((eulerian_pdel_variational_theorem Q G K P F t0).mp hs p hp).2.2.2
  refine ⟨?_,P.entropy_production_nonnegative K p⟩
  have h := congrArg (fun f : Scalar => f p) (P.entropy_identity_off_shell K)
  simpa [he] using h

namespace Box

/-- Three-dimensional energy of the fixed spatial box at a stated time. -/
def sliceEnergy (Q : Box) (u : Scalar) (t : ℝ) : ℝ :=
  ∫ y in Set.Icc (Q.lo ∘ (0 : Fin 4).succAbove) (Q.hi ∘ (0 : Fin 4).succAbove),
    u ((0 : Fin 4).insertNth t y)

/-- Six actual side-face integrals, including the time coordinate on each face. -/
def spatialBoundaryFlux (Q : Box) (F : Vector) : ℝ :=
  ∑ i : Fin 3,
    ((∫ y in Set.Icc (Q.lo ∘ i.succ.succAbove) (Q.hi ∘ i.succ.succAbove),
        F i (i.succ.insertNth (Q.hi i.succ) y)) -
     (∫ y in Set.Icc (Q.lo ∘ i.succ.succAbove) (Q.hi ∘ i.succ.succAbove),
        F i (i.succ.insertNth (Q.lo i.succ) y)))

theorem boundary_current_decomposition (Q : Box) (u : Scalar) (F : Vector) :
    Q.boundaryFlux (spacetimeCurrent u F) =
      Q.sliceEnergy u (Q.hi 0)-Q.sliceEnergy u (Q.lo 0)+Q.spatialBoundaryFlux F := by
  unfold boundaryFlux sliceEnergy spatialBoundaryFlux
  rw [Fin.sum_univ_succ]
  have hF : ![F 0,F 1,F 2] = F := by
    funext i
    fin_cases i <;> rfl
  simp [spacetimeCurrent,hF]

end Box

/-- Finite-interval energy balance on a fixed Eulerian spatial box. This is an
actual integral identity with all side-face powers, NOT a coefficient budget. -/
theorem integrated_energy_from_stationarity
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hmass : MassAdmissible Q P) (hs : Stationary Q G K P F t0) :
    Q.sliceEnergy (P.totalEnergy G) (Q.hi 0)-
      Q.sliceEnergy (P.totalEnergy G) (Q.lo 0)+
      Q.spatialBoundaryFlux (P.totalEnergyFlux G K)=0 := by
  have he := energy_from_stationarity Q G K P F t0 hmass hs
  have hz : Q.integral (P.energyResidual G K)=Q.integral 0 := by
    apply Q.integral_congr
    intro p hp
    exact he p hp
  change Q.integral (dt (P.totalEnergy G)+div (P.totalEnergyFlux G K))=Q.integral 0 at hz
  rw [← div4_current] at hz
  rw [Q.integral_divergence,Q.boundary_current_decomposition,Q.integral_zero] at hz
  exact hz

/-- One compact conclusion collecting the full variational equations, genuine
induction, temperature, local energy, and nonnegative entropy production. -/
theorem eulerian_pdel_mhd_and_energy
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hmass : MassAdmissible Q P) (hs : Stationary Q G K P F t0) :
    EulerianMHDOn Q G K P ∧
    (∀ p ∈ Q.interior, (∀ i, P.inductionResidual K i p=0) ∧
      P.temperatureResidual G K p=0) ∧
    (∀ p ∈ Q.closed, P.energyResidual G K p=0 ∧
      conservative P.velocity P.state.entropy p+div (P.entropyFlux K) p=
        P.entropyProduction K p ∧ 0 ≤ P.entropyProduction K p) := by
  refine ⟨(eulerian_pdel_mhd_theorem Q G K P F t0 hmass).mp hs,?_,?_⟩
  · intro p hp
    exact ⟨induction_from_stationarity Q G K P F t0 hs hp,
      temperature_from_stationarity Q G K P F t0 hmass hs hp⟩
  · intro p hp
    exact ⟨energy_from_stationarity Q G K P F t0 hmass hs p hp,
      entropy_from_stationarity Q G K P F t0 hs hp⟩

end PdelEulerian
