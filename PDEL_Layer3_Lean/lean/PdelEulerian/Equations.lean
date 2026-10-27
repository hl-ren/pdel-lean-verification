import PdelEulerian.Stationarity

noncomputable section
open Set
namespace PdelEulerian

namespace Fields

/-- Mass-corrected, physical Lorentz momentum residual. -/
def physicalMomentum (G : Gas) (K : Transport) (P : Fields) : Vector :=
  scale P.state.rho (materialV P.velocity P.velocity)+grad (P.state.pressure G)-
    divTensor (P.viscousStress K)-cross P.current P.magnetic

def ohmDefect (K : Transport) (P : Fields) : Vector :=
  P.electric+cross P.velocity P.magnetic-matvec K.eta P.current

def physicalThermalPower (K : Transport) (P : Fields) : Scalar :=
  dot P.current (matvec K.eta P.current)+P.viscousPower K

def physicalEntropy (K : Transport) (P : Fields) : Scalar :=
  P.state.temp*conservative P.velocity P.state.entropy+div (P.heatFlux K)-
    P.physicalThermalPower K

def inductionResidual (K : Transport) (P : Fields) : Vector :=
  dtV P.magnetic-curl (cross P.velocity P.magnetic)+curl (matvec K.eta P.current)

/-- Algebraic relation between the computed coefficient and the full momentum
operator; this exposes exactly where mass admissibility is used. -/
theorem physical_momentum_identity (G : Gas) (K : Transport) (P : Fields) :
    P.physicalMomentum G K=P.momentumResidual G K-
      scale P.densityResidual P.velocity+cross P.magnetic (P.ohmResidual K) := by
  unfold physicalMomentum momentumResidual densityResidual ohmResidual
  rw [conservative_momentum_split]
  funext i
  fin_cases i <;> simp [scale,cross,Matrix.vecHead,Matrix.vecTail,Function.comp_def] <;> ring

theorem ohm_defect_identity (K : Transport) (P : Fields) :
    P.ohmDefect K = -matvec K.eta (P.ohmResidual K) := by
  have h := K.eta_sigma P.relativeRate
  change matvec K.eta (P.resistance K)=P.relativeRate at h
  rw [ohmDefect, P.relative_electric_identity, ← h]
  funext i
  simp [ohmResidual, matvec]
  ring

theorem ohm_residual_from_defect (K : Transport) (P : Fields) {p : ST}
    (h : ∀ i, P.ohmDefect K i p=0) : ∀ i, P.ohmResidual K i p=0 := by
  have hr : ∀ i, matvec K.eta (P.ohmResidual K) i p=0 := by
    intro i
    have hi := h i
    rw [ohm_defect_identity] at hi
    simpa only [Pi.neg_apply, eval_neg, neg_eq_zero] using hi
  have hid := K.sigma_eta (P.ohmResidual K)
  intro i
  have hi := congrArg (fun v : Vector => v i p) hid
  change K.sigma i 0 p * matvec K.eta (P.ohmResidual K) 0 p +
    K.sigma i 1 p * matvec K.eta (P.ohmResidual K) 1 p +
    K.sigma i 2 p * matvec K.eta (P.ohmResidual K) 2 p = P.ohmResidual K i p at hi
  simpa only [hr, mul_zero, add_zero] using hi.symm

theorem ohm_defect_from_residual (K : Transport) (P : Fields) {p : ST}
    (h : ∀ i, P.ohmResidual K i p=0) : ∀ i, P.ohmDefect K i p=0 := by
  intro i
  rw [ohm_defect_identity]
  simp [matvec,h]

theorem physical_entropy_from_residual (K : Transport) (P : Fields) {p : ST}
    (hA : ∀ i, P.ohmResidual K i p=0) :
    P.physicalEntropy K p=P.entropyResidual K p := by
  simp only [physicalEntropy, physicalThermalPower, entropyResidual,
    eval_add, eval_sub]
  rw [P.joule_on_ohm K hA]
  ring

/-- Faraday is kinematic; full induction is the curl of the independently derived
Ohm equation. The two do not require dividing by a component of B. -/
theorem induction_defect_identity (K : Transport) (P : Fields) :
    P.inductionResidual K = -curl (P.ohmDefect K) := by
  have hf := P.faraday_identity
  unfold ohmDefect inductionResidual
  rw [curl_sub,curl_add]
  funext i
  have hi := congrArg (fun v : Vector => v i) hf
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at hi ⊢
  linear_combination hi

end Fields

/-- Physical potential formulation. The current and Faraday identities are
kinematic definitions; the full vector Ohm relation is retained, not replaced by
its curl. Curl alone would lose a gradient/harmonic electric-field constraint. -/
def EulerianMHDOn (Q : Box) (G : Gas) (K : Transport) (P : Fields) : Prop :=
  ∀ p ∈ Q.closed,
    P.densityResidual p=0 ∧
    (∀ i, P.physicalMomentum G K i p=0) ∧
    (∀ i, P.ohmDefect K i p=0) ∧
    P.state.entropy p = -P.state.phiTemp G p ∧
    P.physicalEntropy K p=0

/-- Mass admissibility is deliberately a separate kinematic condition. -/
def MassAdmissible (Q : Box) (P : Fields) : Prop :=
  ∀ p ∈ Q.closed, P.densityResidual p=0

/-- The central Layer-3 statement for the potential formulation. No momentum,
Ohm, thermal-conjugacy or entropy equation is assumed in Fields or MaterialChart. -/
theorem eulerian_pdel_mhd_theorem
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (hmass : MassAdmissible Q P) :
    Stationary Q G K P F t0 ↔ EulerianMHDOn Q G K P := by
  rw [eulerian_pdel_variational_theorem]
  constructor
  · intro h p hp
    rcases h p hp with ⟨hm,hA,hT,hS⟩
    refine ⟨hmass p hp,?_,P.ohm_defect_from_residual K hA,?_,?_⟩
    · intro i
      rw [P.physical_momentum_identity G K]
      fin_cases i <;> simp [scale,cross,hm,hA,hmass p hp]
    · have ht : P.state.phiTemp G p+P.state.entropy p=0 := hT
      linarith
    · rw [P.physical_entropy_from_residual K hA]
      exact hS
  · intro h p hp
    rcases h p hp with ⟨hr,hm,hO,hT,hS⟩
    have hA := P.ohm_residual_from_defect K hO
    refine ⟨?_,hA,?_,?_⟩
    · intro i
      have hi := hm i
      rw [P.physical_momentum_identity G K] at hi
      fin_cases i <;> simpa [scale,cross,hA,hr] using hi
    · change P.state.phiTemp G p+P.state.entropy p=0
      rw [hT]
      ring
    · rw [← P.physical_entropy_from_residual K hA]
      exact hS

/-- A material density constraint supplies the mass premise of the central
variational theorem by differentiation. It is not an extra physical balance law. -/
theorem eulerian_pdel_mhd_from_material_motion
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (rhoRef : Label → ℝ)
    (hmass : ∀ t X, P.state.rho (F.position t X)*F.volumeFactor t X=rhoRef X) :
    Stationary Q G K P F t0 ↔ EulerianMHDOn Q G K P := by
  apply eulerian_pdel_mhd_theorem
  have h := F.mass_conservation P.state.rho rhoRef hmass
  intro p _
  exact congrArg (fun f : Scalar => f p) h

/-- Explicit connection between the thermal stationary coefficient and the
ordinary derivative of the actual ideal-gas free energy. -/
theorem thermal_conjugacy_from_stationarity
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hs : Stationary Q G K P F t0) {p : ST} (hp : p ∈ Q.closed) :
    P.state.entropy p =
      -deriv (fun T => ThermalState.freeEnergyReal G (P.state.rho p) T) (P.state.temp p) := by
  have h := ((eulerian_pdel_variational_theorem Q G K P F t0).mp hs p hp).2.2.1
  rw [ThermalState.temperature_partial_derivative]
  change P.state.phiTemp G p+P.state.entropy p=0 at h
  linarith

/-- Only interior points have the neighborhood needed for differentiating Ohm.
This is a full vector induction equation, not a scalar energetic projection. -/
theorem induction_from_stationarity
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hs : Stationary Q G K P F t0) {p : ST} (hp : p ∈ Q.interior) :
    ∀ i, P.inductionResidual K i p=0 := by
  have hprim := (eulerian_pdel_variational_theorem Q G K P F t0).mp hs
  have he : ∀ q ∈ Q.interior, ∀ i, P.ohmDefect K i q=0 := by
    intro q hq
    exact P.ohm_defect_from_residual K (hprim q (Q.interior_subset hq)).2.1
  have hd : ∀ i j, d j (P.ohmDefect K i) p=0 := by
    intro i j
    exact d_eq_zero_on_open Q.interior_open (P.ohmDefect K i)
      (fun q hq => he q hq i) hp j
  rw [P.induction_defect_identity K]
  intro i
  fin_cases i <;> simp only [Fin.reduceFinMk,curl,dx,Pi.neg_apply,eval_neg,eval_sub,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,hd,sub_self,neg_zero]

end PdelEulerian
