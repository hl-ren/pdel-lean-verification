import PdelEulerian.Energy

/-!
# Optional literal derivative-of-integral bridge

The primary PDEL operation is the integral of computed local mixed derivatives.
This module additionally identifies it with the derivative of the actual finite
mixed-action family, under explicitly stated dominated-differentiation data.

Those analytic bounds are not MHD equations. They are NOT silently inferred from
the weaker MaterialChart record, which only controls characteristics in time.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace PdelEulerian

/-- An actual parameterized action, not an expression defined from residuals. -/
def mixedAction (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) (e : ℝ) : ℝ :=
  Q.integrate (mixedDensity G K P F t0 V e)

theorem mixedAction_at_zero (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) :
    mixedAction Q G K P F t0 V 0=stateHistoryAction Q G K P F t0 := by
  unfold mixedAction stateHistoryAction Box.integrate
  simp_rw [mixedDensity_at_zero]

/-- Explicit regularity for differentiating the actual action under its integral.
In particular, the derivative itself is proved below, not supplied in this record. -/
structure ActionRegular (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test) : Prop where
  domination : ∃ (radius : ℝ) (bound : ST → ℝ), 0 < radius ∧
    (∀ᶠ e in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (mixedDensity G K P F t0 V e) (volume.restrict Q.closed)) ∧
    Integrable (mixedDensity G K P F t0 V 0) (volume.restrict Q.closed) ∧
    (∀ᵐ p ∂(volume.restrict Q.closed),
      LipschitzOnWith (Real.nnabs (bound p))
        (fun e => mixedDensity G K P F t0 V e p) (ball 0 radius)) ∧
    Integrable bound (volume.restrict Q.closed)

theorem mixedAction_hasDerivAt
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ) (V : Test)
    (hreg : ActionRegular Q G K P F t0 V) :
    HasDerivAt (mixedAction Q G K P F t0 V)
      (firstVariation Q G K P F t0 V) 0 := by
  rcases hreg.domination with ⟨radius,bound,hradius,hmeas,hbase,hlip,hbound⟩
  have hderiv : ∀ᵐ p ∂(volume.restrict Q.closed),
      HasDerivAt (fun e => mixedDensity G K P F t0 V e p)
        (rawVariation G K P V p) 0 :=
    Filter.Eventually.of_forall (fun p => mixedDensity_hasDerivAt G K P F t0 V p)
  have hwmeas : AEStronglyMeasurable (rawVariation G K P V : ST → ℝ)
      (volume.restrict Q.closed) := (rawVariation G K P V).continuous.aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun e p => mixedDensity G K P F t0 V e p)
    (F' := fun p => rawVariation G K P V p)
    (μ := volume.restrict Q.closed) (x₀ := (0 : ℝ))
    hradius hmeas hbase hwmeas hlip hbound hderiv
  rw [firstVariation_raw]
  simpa only [mixedAction, Box.integral, Box.integrate] using h.2

/-- The same equivalence with a literal mixed-action parameter derivative.
All domination hypotheses remain visible in the theorem statement. -/
theorem literal_action_stationarity_iff
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hmass : MassAdmissible Q P)
    (hreg : ∀ V, Admissible Q V → ActionRegular Q G K P F t0 V) :
    (∀ V, Admissible Q V → deriv (mixedAction Q G K P F t0 V) 0=0) ↔
      EulerianMHDOn Q G K P := by
  rw [← eulerian_pdel_mhd_theorem Q G K P F t0 hmass]
  constructor
  · intro h V hV
    have hv := (mixedAction_hasDerivAt Q G K P F t0 V (hreg V hV)).deriv
    rw [← hv]
    exact h V hV
  · intro h V hV
    rw [(mixedAction_hasDerivAt Q G K P F t0 V (hreg V hV)).deriv]
    exact h V hV

/-- A finite base action and the derived governing equations can be certified
simultaneously, without identifying a derivative with an assumed PDE. -/
theorem finite_action_and_mhd
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hH : HistoryIntegrable Q K P F t0) (hmass : MassAdmissible Q P)
    (hs : Stationary Q G K P F t0) :
    IntegrableOn (stateHistoryDensity G K P F t0) Q.closed ∧
      EulerianMHDOn Q G K P := by
  exact ⟨stateHistoryAction_integrable Q G K P F t0 hH,
    (eulerian_pdel_mhd_theorem Q G K P F t0 hmass).mp hs⟩

end PdelEulerian
