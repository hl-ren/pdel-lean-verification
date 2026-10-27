import PdelBridge.Thermal
import PdelEulerian.Examples

noncomputable section
open Set PdelEulerian
open scoped ContDiff
namespace PdelBridge

def restPoint (t : ℝ) (X : Label) : ST := ![t,X 0,X 1,X 2]
def timeTrace (f : Scalar) (X : Label) (t : ℝ) : ℝ := f (restPoint t X)

theorem time_trace_smooth (f : Scalar) (X : Label) : ContDiff ℝ ∞ (timeTrace f X) := by
  have hp : ContDiff ℝ ∞ (fun t => restPoint t X) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun t : ℝ => t)
      exact contDiff_id
    · change ContDiff ℝ ∞ (fun _ : ℝ => X 0)
      exact contDiff_const
    · change ContDiff ℝ ∞ (fun _ : ℝ => X 1)
      exact contDiff_const
    · change ContDiff ℝ ∞ (fun _ : ℝ => X 2)
      exact contDiff_const
  exact f.smooth.comp hp

theorem time_trace_hasDerivAt (f : Scalar) (X : Label) (t : ℝ) :
    HasDerivAt (timeTrace f X) (dt f (restPoint t X)) t := by
  have h := Example.chart.along_flow_hasDerivAt f t X
  change HasDerivAt (timeTrace f X) (material (0 : Vector) f (restPoint t X)) t at h
  simpa only [material,adv,dot,Pi.zero_apply,zero_mul,zero_add,add_zero] using h

def restFields (G : Gas) (temp entropy : Scalar) (ht : ∀ p, 0 < temp p)
    (potential : Vector) : Fields :=
  ⟨referenceState G temp entropy ht, 0, potential⟩

def thermalTracePath (temp entropy : Scalar) (ht : ∀ p, 0 < temp p) (X : Label) :
    PdelBasic.Path where
  x := fun _ => 0
  v := fun _ => 0
  acc := fun _ => 0
  theta := timeTrace temp X
  entropy := timeTrace entropy X
  x_c1 := contDiff_const
  v_c1 := contDiff_const
  acc_c1 := contDiff_const
  theta_c1 := (time_trace_smooth temp X).of_le (by simp)
  entropy_c1 := (time_trace_smooth entropy X).of_le (by simp)
  dx := fun t => hasDerivAt_const t 0
  dv := fun t => hasDerivAt_const t 0
  theta_pos := fun t => ht (restPoint t X)

def thermalTraceLoads (K : Transport) (P : Fields) (X : Label) : PdelBasic.Loads where
  force := fun _ => 0
  heatOut := timeTrace (div (P.heatFlux K) - P.joulePower K - P.viscousPower K) X
  force_c1 := contDiff_const
  heatOut_cont := (time_trace_smooth _ X).continuous

theorem rest_point_in_box (Q : Box) (X : Label)
    (hX : ∀ i : Fin 3, Q.lo i.succ ≤ X i ∧ X i ≤ Q.hi i.succ)
    {t : ℝ} (ht : t ∈ Icc (Q.lo 0) (Q.hi 0)) : restPoint t X ∈ Q.closed := by
  rw [Q.mem_closed]
  intro i
  fin_cases i
  · exact ht
  · exact hX 0
  · exact hX 1
  · exact hX 2

/-- An actual one-way dynamical reduction: at rest and fixed reference density,
the MHD thermal trajectory is a Layer-2 stationary zero-displacement path.
The imported heat includes the EM power, rather than relabeling it as viscosity. -/
theorem thermal_projection_stationary (G : Gas) (K : Transport)
    (temp entropy : Scalar) (ht : ∀ p, 0 < temp p) (potential : Vector)
    (Q : Box) (F : MaterialChart (restFields G temp entropy ht potential).velocity)
    (t0 viscosity : ℝ) (hv : 0 ≤ viscosity) (X : Label)
    (hX : ∀ i : Fin 3, Q.lo i.succ ≤ X i ∧ X i ≤ Q.hi i.succ)
    (hs : Stationary Q G K (restFields G temp entropy ht potential) F t0) :
    PdelBasic.Stationary (referenceMaterial G viscosity hv) (thermalTracePath temp entropy ht X)
      (thermalTraceLoads K (restFields G temp entropy ht potential) X) (Q.lo 0) (Q.hi 0) := by
  apply (PdelBasic.pdel_basic_variational_theorem _ _ _ (Q.strict 0)).mpr
  intro t htime
  have hp := rest_point_in_box Q X hX htime
  obtain ⟨hm,hA,hT,hS⟩ := (eulerian_pdel_variational_theorem Q G K
    (restFields G temp entropy ht potential) F t0).mp hs (restPoint t X) hp
  refine ⟨?_,?_,?_⟩
  · simp [thermalTracePath, thermalTraceLoads, referenceMaterial,
      PdelBasic.elasticForce, PdelBasic.viscousForce]
  · change entropy (restPoint t X) =
      PdelBasic.entropyState (referenceMaterial G viscosity hv) 0 (temp (restPoint t X))
    rw [entropy_reference G viscosity hv temp entropy ht 0 (restPoint t X)]
    change (referenceState G temp entropy ht).phiTemp G (restPoint t X) +
      entropy (restPoint t X) = 0 at hT
    linarith
  · change temp (restPoint t X) * deriv (timeTrace entropy X) t +
      (div ((restFields G temp entropy ht potential).heatFlux K) -
        (restFields G temp entropy ht potential).joulePower K -
        (restFields G temp entropy ht potential).viscousPower K) (restPoint t X) =
          PdelBasic.dissipation (referenceMaterial G viscosity hv) 0
    rw [(time_trace_hasDerivAt entropy X t).deriv]
    simp only [Fields.entropyResidual,restFields,referenceState,conservative,
      scale,Pi.zero_apply,mul_zero,div,dx_zero,add_zero,
      eval_add,eval_sub,eval_mul,PdelBasic.dissipation,PdelBasic.viscousForce] at hS ⊢
    linarith

theorem projected_temperature_equation (G : Gas) (K : Transport)
    (temp entropy : Scalar) (ht : ∀ p, 0 < temp p) (potential : Vector)
    (Q : Box) (F : MaterialChart (restFields G temp entropy ht potential).velocity)
    (t0 viscosity : ℝ) (hv : 0 ≤ viscosity) (X : Label)
    (hX : ∀ i : Fin 3, Q.lo i.succ ≤ X i ∧ X i ≤ Q.hi i.succ)
    (hs : Stationary Q G K (restFields G temp entropy ht potential) F t0)
    {t : ℝ} (htime : t ∈ Ioo (Q.lo 0) (Q.hi 0)) :
    G.rhoRef * G.cv * deriv (timeTrace temp X) t +
      (thermalTraceLoads K (restFields G temp entropy ht potential) X).heatOut t = 0 := by
  have h := PdelBasic.temperature_equation_from_stationarity _ _ _ (Q.strict 0)
    (thermal_projection_stationary G K temp entropy ht potential Q F t0 viscosity hv X hX hs) htime
  simpa only [referenceMaterial,thermalTracePath,zero_mul,add_zero,
    PdelBasic.dissipation,PdelBasic.viscousForce,mul_zero] using h

/-- The nonzero-current, strictly positive-Joule witness in Layer 3 projects
to an actual Layer-2 stationary thermal path. -/
theorem example_thermal_projection (Q : Box) (X : Label)
    (hX : ∀ i : Fin 3, Q.lo i.succ ≤ X i ∧ X i ≤ Q.hi i.succ) :
    PdelBasic.Stationary (referenceMaterial Example.gas 0 le_rfl)
      (thermalTracePath Example.temp (slog Example.temp Example.temp_nonzero) Example.temp_positive X)
      (thermalTraceLoads Example.transport Example.fields X) (Q.lo 0) (Q.hi 0) := by
  exact thermal_projection_stationary Example.gas Example.transport Example.temp
    (slog Example.temp Example.temp_nonzero) Example.temp_positive Example.fields.potential
    Q Example.chart 0 0 le_rfl X hX (Example.example_stationary Q 0)

end PdelBridge
