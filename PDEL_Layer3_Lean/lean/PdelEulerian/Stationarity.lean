import PdelEulerian.BoxIntegration

/-!
# From the single mixed differential to independent Eulerian equations

Stationarity means an actual integral vanishes for every smooth boundary-zero
quadruple of independent test fields.  It is not defined coefficientwise.
-/

noncomputable section
open Set MeasureTheory
namespace PdelEulerian

/-- Boundary-zero directions form a linear, sufficiently rich subspace. No
boundary condition is imposed on rho, T, s, v, or A by this definition. -/
structure Admissible (Q : Box) (V : Test) : Prop where
  xi_zero : ∀ i, Q.VanishesOnFaces (V.xi i)
  a_zero : ∀ i, Q.VanishesOnFaces (V.a i)
  temperature_zero : Q.VanishesOnFaces V.temperature
  entropy_zero : Q.VanishesOnFaces V.entropySelector

/-- The integral of actual local mixed parameter derivatives. The input density
contains storage and committed histories, not residuals. -/
def firstVariation (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) : ℝ :=
  Q.integrate (fun p => deriv (fun e => mixedDensity G K P F t0 V e p) 0)

def stateHistoryAction (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) : ℝ :=
  Q.integrate (stateHistoryDensity G K P F t0)

/-- Required only if one also wants the numerical value of the unperturbed
Bochner action. The differential theorem proves integrability of its derivative
without assuming any governing residual. -/
structure HistoryIntegrable (Q : Box) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) : Prop where
  heat : IntegrableOn (F.currentHistory (div (P.heatFlux K)) t0) Q.closed
  joule : IntegrableOn (F.currentHistory (P.joulePower K) t0) Q.closed
  viscous : IntegrableOn (F.currentHistory (P.viscousPower K) t0) Q.closed

/-- Primitive coefficients, named only after differentiating and performing
integration by parts. Conjugacy is not a path assumption. -/
def PrimitiveOn (Q : Box) (G : Gas) (K : Transport) (P : Fields) : Prop :=
  ∀ p ∈ Q.closed,
    (∀ i, P.momentumResidual G K i p=0) ∧
    (∀ i, P.ohmResidual K i p=0) ∧
    P.thermalResidual G p=0 ∧ P.entropyResidual K p=0

def Stationary (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) : Prop :=
  ∀ V : Test, Admissible Q V → firstVariation Q G K P F t0 V=0

theorem firstVariation_is_integrable (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) :
    IntegrableOn (fun p => deriv (fun e => mixedDensity G K P F t0 V e p) 0) Q.closed := by
  simp_rw [actual_local_first_variation]
  exact Q.integrable (rawVariation G K P V)

theorem stateHistoryAction_integrable (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (h : HistoryIntegrable Q K P F t0) :
    IntegrableOn (stateHistoryDensity G K P F t0) Q.closed := by
  have hs : IntegrableOn
      (fun p => P.kinetic p-P.state.freeEnergy G p-P.state.temp p*P.state.entropy p-
        normSq P.magnetic p/2) Q.closed := by
    convert Q.integrable (P.kinetic-P.state.freeEnergy G-P.state.temp*P.state.entropy-
      C (1/2)*normSq P.magnetic) using 1
    funext p
    simp only [eval_sub,eval_mul,eval_C]
    ring
  exact ((hs.sub h.heat).add h.joule).add h.viscous

theorem firstVariation_raw (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) :
    firstVariation Q G K P F t0 V=Q.integral (rawVariation G K P V) := by
  unfold firstVariation Box.integral
  simp_rw [actual_local_first_variation]

/-- No boundary work has been silently deleted: it is represented explicitly. -/
theorem firstVariation_with_boundary (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) :
    firstVariation Q G K P F t0 V =
      -Q.integral (residualPairing G K P V)+Q.boundaryFlux (variationCurrent G K P V) := by
  rw [firstVariation_raw, first_variation_divergence_identity,
    Q.integral_add, Q.integral_neg, Q.integral_divergence]

theorem variationCurrent_boundary_zero (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (V : Test) (hV : Admissible Q V) :
    ∀ i, Q.VanishesOnFaces (variationCurrent G K P V i) := by
  intro i j p hp
  have hx := fun k => hV.xi_zero k j p hp
  have ha := fun k => hV.a_zero k j p hp
  fin_cases i <;>
    simp [variationCurrent, spacetimeCurrent, scale, matvec, transpose,
      cross, dot, hx, ha]

theorem firstVariation_residual (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) (hV : Admissible Q V) :
    firstVariation Q G K P F t0 V = -Q.integral (residualPairing G K P V) := by
  rw [firstVariation_with_boundary,
    Q.boundaryFlux_zero _ (variationCurrent_boundary_zero Q G K P V hV), add_zero]

/-- A real three-component test, not a projection along the physical velocity. -/
def oneComponent (i : Fin 3) (f : Scalar) : Vector := fun j => if i=j then f else 0

theorem dot_oneComponent (v : Vector) (i : Fin 3) (f : Scalar) :
    dot v (oneComponent i f)=v i*f := by
  fin_cases i <;> simp [dot, oneComponent]

def momentumTest (Q : Box) (R : Vector) (i : Fin 3) : Test :=
  ⟨oneComponent i (Q.weight*R i),0,0,0⟩
def potentialTest (Q : Box) (R : Vector) (i : Fin 3) : Test :=
  ⟨0,oneComponent i (Q.weight*R i),0,0⟩
def temperatureTest (Q : Box) (R : Scalar) : Test := ⟨0,0,Q.weight*R,0⟩
def entropyTest (Q : Box) (R : Scalar) : Test := ⟨0,0,0,Q.weight*R⟩

theorem oneComponent_vanishes (Q : Box) {f : Scalar} (hf : Q.VanishesOnFaces f)
    (i j : Fin 3) : Q.VanishesOnFaces (oneComponent i f j) := by
  by_cases h : i=j
  · simpa [oneComponent, h] using hf
  · simpa [oneComponent, h] using Q.zero_vanishes

theorem momentumTest_admissible (Q : Box) (R : Vector) (i : Fin 3) :
    Admissible Q (momentumTest Q R i) := by
  exact ⟨fun j => oneComponent_vanishes Q (Q.mul_vanishes Q.weight_vanishes (R i)) i j,
    fun _ => Q.zero_vanishes,Q.zero_vanishes,Q.zero_vanishes⟩

theorem potentialTest_admissible (Q : Box) (R : Vector) (i : Fin 3) :
    Admissible Q (potentialTest Q R i) := by
  exact ⟨fun _ => Q.zero_vanishes,
    fun j => oneComponent_vanishes Q (Q.mul_vanishes Q.weight_vanishes (R i)) i j,
    Q.zero_vanishes,Q.zero_vanishes⟩

theorem temperatureTest_admissible (Q : Box) (R : Scalar) :
    Admissible Q (temperatureTest Q R) := by
  exact ⟨fun _ => Q.zero_vanishes,fun _ => Q.zero_vanishes,
    Q.mul_vanishes Q.weight_vanishes R,Q.zero_vanishes⟩

theorem entropyTest_admissible (Q : Box) (R : Scalar) :
    Admissible Q (entropyTest Q R) := by
  exact ⟨fun _ => Q.zero_vanishes,fun _ => Q.zero_vanishes,
    Q.zero_vanishes,Q.mul_vanishes Q.weight_vanishes R⟩

/-- The main integral variational theorem: actual mixed differentiation,
actual 4D integration by parts, and a proved localization argument. -/
theorem eulerian_pdel_variational_theorem
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) :
    Stationary Q G K P F t0 ↔ PrimitiveOn Q G K P := by
  constructor
  · intro hs
    have hm : ∀ i, ∀ p ∈ Q.closed, P.momentumResidual G K i p=0 := by
      intro i
      apply Q.weighted_square_localization
      have h := hs (momentumTest Q (P.momentumResidual G K) i)
        (momentumTest_admissible Q _ i)
      rw [firstVariation_residual Q G K P F t0 _
        (momentumTest_admissible Q _ i)] at h
      have heq : residualPairing G K P (momentumTest Q (P.momentumResidual G K) i)=
          Q.weight*(P.momentumResidual G K i)^2 := by
        simp only [residualPairing, momentumTest, dot_oneComponent]
        simp [dot]
        ring
      rw [heq, neg_eq_zero] at h
      exact h
    have ha : ∀ i, ∀ p ∈ Q.closed, P.ohmResidual K i p=0 := by
      intro i
      apply Q.weighted_square_localization
      have h := hs (potentialTest Q (P.ohmResidual K) i)
        (potentialTest_admissible Q _ i)
      rw [firstVariation_residual Q G K P F t0 _
        (potentialTest_admissible Q _ i)] at h
      have heq : residualPairing G K P (potentialTest Q (P.ohmResidual K) i)=
          Q.weight*(P.ohmResidual K i)^2 := by
        simp only [residualPairing, potentialTest, dot_oneComponent]
        simp [dot]
        ring
      rw [heq, neg_eq_zero] at h
      exact h
    have ht : ∀ p ∈ Q.closed, P.thermalResidual G p=0 := by
      apply Q.weighted_square_localization
      have h := hs (temperatureTest Q (P.thermalResidual G))
        (temperatureTest_admissible Q _)
      rw [firstVariation_residual Q G K P F t0 _
        (temperatureTest_admissible Q _)] at h
      have heq : residualPairing G K P (temperatureTest Q (P.thermalResidual G))=
          Q.weight*(P.thermalResidual G)^2 := by
        simp [residualPairing, temperatureTest, dot]
        ring
      rw [heq, neg_eq_zero] at h
      exact h
    have he : ∀ p ∈ Q.closed, P.entropyResidual K p=0 := by
      apply Q.weighted_square_localization
      have h := hs (entropyTest Q (P.entropyResidual K))
        (entropyTest_admissible Q _)
      rw [firstVariation_residual Q G K P F t0 _
        (entropyTest_admissible Q _)] at h
      have heq : residualPairing G K P (entropyTest Q (P.entropyResidual K))=
          Q.weight*(P.entropyResidual K)^2 := by
        simp [residualPairing, entropyTest, dot]
        ring
      rw [heq, neg_eq_zero] at h
      exact h
    intro p hp
    exact ⟨fun i => hm i p hp,fun i => ha i p hp,ht p hp,he p hp⟩
  · intro hpde V hV
    rw [firstVariation_residual Q G K P F t0 V hV]
    have hzero : Q.integral (residualPairing G K P V)=Q.integral 0 := by
      apply Q.integral_congr
      intro p hp
      rcases hpde p hp with ⟨hm,ha,ht,hs⟩
      simp [residualPairing, dot, hm,ha,ht,hs]
    rw [hzero,Q.integral_zero,neg_zero]

end PdelEulerian
