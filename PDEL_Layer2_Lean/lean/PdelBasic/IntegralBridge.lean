import PdelBasic.Stationarity

/-!
# Optional analytic bridge: a derivative of the finite mixed-jet action

`firstVariation` is defined by the PDEL integral of local operations.  This file
ALSO relates it to HasDerivAt of `mixedAction` under explicit dominated
regularity.  No differentiation-under-integral rule is assumed as an axiom.
The hypotheses below are measurability, integrability and a uniform local
Lipschitz bound; they do not contain the governing equations or the derivative
that we are trying to prove.  We do not claim to have formalized the general
theorem that these bounds follow automatically for every positive C1 path.
-/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology Interval
namespace PdelBasic

/-- Sufficient analytic hypotheses for moving the MIXED-jet derivative under the integral. -/
theorem mixedAction_hasDerivAt (M : Material) (P : Path) (L : Loads)
    {a b radius : ℝ} (hab : a ≤ b) (V : Variation a b)
    (hradius : 0 < radius) (bound : ℝ → ℝ)
    (hmeas : ∀ᶠ e in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (mixedDensity M P L V e) (volume.restrict (Ioc a b)))
    (hbase : Integrable (mixedDensity M P L V 0) (volume.restrict (Ioc a b)))
    (hlip : ∀ᵐ t ∂(volume.restrict (Ioc a b)),
      LipschitzOnWith (Real.nnabs (bound t))
        (fun e => mixedDensity M P L V e t) (ball 0 radius))
    (hbound : Integrable bound (volume.restrict (Ioc a b))) :
    HasDerivAt (mixedAction M P L V) (firstVariation M P L V) 0 := by
  have hderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)),
      HasDerivAt (fun e => mixedDensity M P L V e t) (weakDensity M P L V t) 0 :=
    Filter.Eventually.of_forall (fun t => mixedDensity_hasDerivAt M P L V t)
  have hwmeas : AEStronglyMeasurable (weakDensity M P L V)
      (volume.restrict (Ioc a b)) := (weakDensity_continuous M P L V).aestronglyMeasurable
  have hi := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := mixedDensity M P L V) (F' := weakDensity M P L V)
    (μ := volume.restrict (Ioc a b)) (x₀ := (0 : ℝ))
    hradius hmeas hbase hwmeas hlip hbound hderiv
  rw [firstVariation_raw]
  change HasDerivAt (fun e => ∫ t in a..b, mixedDensity M P L V e t)
    (∫ t in a..b, weakDensity M P L V t) 0
  simpa only [intervalIntegral.integral_of_le hab] using hi.2

/-- Explicit domination data; no Euler--Lagrange equation is among these conditions. -/
def IntegralRegular (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (V : Variation a b) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧ ∃ bound : ℝ → ℝ,
    (∀ᶠ e in 𝓝 (0 : ℝ), AEStronglyMeasurable (mixedDensity M P L V e)
      (volume.restrict (Ioc a b))) ∧
    Integrable (mixedDensity M P L V 0) (volume.restrict (Ioc a b)) ∧
    (∀ᵐ t ∂(volume.restrict (Ioc a b)),
      LipschitzOnWith (Real.nnabs (bound t))
        (fun e => mixedDensity M P L V e t) (ball 0 radius)) ∧
    Integrable bound (volume.restrict (Ioc a b))

/-- A literal derivative-of-integral formulation, under standard domination data. -/
theorem mixed_action_stationarity_iff (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b)
    (hreg : ∀ V : Variation a b, IntegralRegular M P L V) :
    (∀ V : Variation a b, deriv (mixedAction M P L V) 0 = 0) ↔
      GoverningOn M P L a b := by
  have hd (V : Variation a b) :
      deriv (mixedAction M P L V) 0 = firstVariation M P L V := by
    rcases hreg V with ⟨radius, hradius, bound, hm, hi, hl, hb⟩
    exact (mixedAction_hasDerivAt M P L hab.le V hradius bound hm hi hl hb).deriv
  simp_rw [hd]
  exact pdel_basic_variational_theorem M P L hab

end PdelBasic
