import PdelBasic.FirstVariation

/-!
# Stationarity iff the governing equations

The localization argument is proved, not postulated as a "fundamental lemma".
A mechanical test `w * residual`, where w=(t-a)^2(b-t)^2, is admissible.
Its pairing is a nonnegative weighted square. Continuity and integral
positivity force the residual to vanish in the interior, then at the endpoints.
Thermal and entropy tests can be varied independently.
-/
noncomputable section
open MeasureTheory Set
open scoped Topology Interval
namespace PdelBasic

def endpointWeight (a b t : ℝ) : ℝ := (t - a)^2 * (b - t)^2

theorem endpointWeight_nonnegative (a b t : ℝ) : 0 ≤ endpointWeight a b t := by
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem endpointWeight_positive {a b t : ℝ} (ht : t ∈ Ioo a b) :
    0 < endpointWeight a b t := by
  exact mul_pos (sq_pos_of_pos (sub_pos.mpr ht.1))
    (sq_pos_of_pos (sub_pos.mpr ht.2))

theorem continuous_zero_from_interior {a b : ℝ} (hab : a < b)
    {F : ℝ → ℝ} (hc : Continuous F) (hz : ∀ t ∈ Ioo a b, F t = 0) :
    ∀ t ∈ Icc a b, F t = 0 := by
  have hclosed : IsClosed {t | F t = 0} := isClosed_eq hc continuous_const
  have hsub : closure (Ioo a b) ⊆ {t | F t = 0} := closure_minimal hz hclosed
  simpa only [closure_Ioo hab.ne] using hsub

theorem weighted_square_localization {a b : ℝ} (hab : a < b)
    {F : ℝ → ℝ} (hc : Continuous F)
    (hz : (∫ t in a..b, F t * (endpointWeight a b t * F t)) = 0) :
    ∀ t ∈ Icc a b, F t = 0 := by
  apply continuous_zero_from_interior hab hc
  intro t ht
  by_contra hne
  have hcG : Continuous (fun u => F u * (endpointWeight a b u * F u)) := by
    unfold endpointWeight
    fun_prop
  have hnonneg : ∀ u, 0 ≤ F u * (endpointWeight a b u * F u) := by
    intro u
    have h := mul_nonneg (endpointWeight_nonnegative a b u) (sq_nonneg (F u))
    nlinarith
  have hpos : 0 < F t * (endpointWeight a b t * F t) := by
    have h := mul_pos (endpointWeight_positive ht) (sq_pos_of_ne_zero hne)
    nlinarith
  have hi : 0 < ∫ u in a..b, F u * (endpointWeight a b u * F u) :=
    intervalIntegral.integral_pos hab hcG.continuousOn
      (fun u _ => hnonneg u) ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, hpos⟩
  rw [hz] at hi
  exact (lt_irrefl (0 : ℝ)) hi

-- Explicit independent test constructors.
def mechanicalTest (a b : ℝ) (F : ℝ → ℝ) (hc : ContDiff ℝ 1 F) : Variation a b where
  h := fun t => endpointWeight a b t * F t
  h_c1 := by dsimp [endpointWeight]; fun_prop
  left := by simp [endpointWeight]
  right := by simp [endpointWeight]
  temperatureTest := fun _ => 0
  temperatureTest_cont := continuous_const
  entropySelector := fun _ => 0
  entropySelector_cont := continuous_const

def thermalTest (a b : ℝ) (F : ℝ → ℝ) (hc : Continuous F) : Variation a b where
  h := fun _ => 0
  h_c1 := contDiff_const
  left := rfl
  right := rfl
  temperatureTest := fun t => endpointWeight a b t * F t
  temperatureTest_cont := by dsimp [endpointWeight]; fun_prop
  entropySelector := fun _ => 0
  entropySelector_cont := continuous_const

def entropyTest (a b : ℝ) (F : ℝ → ℝ) (hc : Continuous F) : Variation a b where
  h := fun _ => 0
  h_c1 := contDiff_const
  left := rfl
  right := rfl
  temperatureTest := fun _ => 0
  temperatureTest_cont := continuous_const
  entropySelector := fun t => endpointWeight a b t * F t
  entropySelector_cont := by dsimp [endpointWeight]; fun_prop

def Stationary (M : Material) (P : Path) (L : Loads) (a b : ℝ) : Prop :=
  ∀ V : Variation a b, firstVariation M P L V = 0

def GoverningOn (M : Material) (P : Path) (L : Loads) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b,
    M.mass * P.acc t + elasticForce M (P.x t) (P.theta t) +
      viscousForce M (P.v t) = L.force t ∧
    P.entropy t = entropyState M (P.x t) (P.theta t) ∧
    P.theta t * deriv P.entropy t + L.heatOut t = dissipation M (P.v t)

theorem integral_zero_on_interval {a b : ℝ} (hab : a ≤ b)
    {F : ℝ → ℝ} (hz : ∀ t ∈ Icc a b, F t = 0) :
    (∫ t in a..b, F t) = 0 := by
  calc
    _ = ∫ t in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply hz t
      simpa only [uIcc_of_le hab] using ht
    _ = 0 := by simp

/-- The equations are conclusions. Only regularity, kinematics and a<b are assumed. -/
theorem stationary_iff_residuals (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) :
    Stationary M P L a b ↔
      ∀ t ∈ Icc a b, mechanicalResidual M P L t = 0 ∧
        thermalResidual M P t = 0 ∧ entropyResidual M P L t = 0 := by
  constructor
  · intro hst
    have hm : ∀ t ∈ Icc a b, mechanicalResidual M P L t = 0 := by
      apply weighted_square_localization hab (mechanicalResidual_c1 M P L).continuous
      have h := hst (mechanicalTest a b (mechanicalResidual M P L)
        (mechanicalResidual_c1 M P L))
      simpa [firstVariation_residual, mechanicalTest] using h
    have hT : ∀ t ∈ Icc a b, thermalResidual M P t = 0 := by
      apply weighted_square_localization hab (thermalResidual_continuous M P)
      have h := hst (thermalTest a b (thermalResidual M P) (thermalResidual_continuous M P))
      simpa [firstVariation_residual, thermalTest] using h
    have hs : ∀ t ∈ Icc a b, entropyResidual M P L t = 0 := by
      apply weighted_square_localization hab (entropyResidual_continuous M P L)
      have h := hst (entropyTest a b (entropyResidual M P L) (entropyResidual_continuous M P L))
      simpa [firstVariation_residual, entropyTest] using h
    exact fun t ht => ⟨hm t ht, hT t ht, hs t ht⟩
  · intro heq V
    have hm : (∫ t in a..b, mechanicalResidual M P L t * V.h t) = 0 := by
      apply integral_zero_on_interval hab.le
      intro t ht
      rw [(heq t ht).1, zero_mul]
    have hT : (∫ t in a..b, thermalResidual M P t * V.temperatureTest t) = 0 := by
      apply integral_zero_on_interval hab.le
      intro t ht
      rw [(heq t ht).2.1, zero_mul]
    have hs : (∫ t in a..b, entropyResidual M P L t * V.entropySelector t) = 0 := by
      apply integral_zero_on_interval hab.le
      intro t ht
      rw [(heq t ht).2.2, zero_mul]
    rw [firstVariation_residual, hm, hT, hs]
    ring

/-- Layer-2 core: mixed stationarity iff momentum, conjugacy and entropy balance. -/
theorem pdel_basic_variational_theorem (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) :
    Stationary M P L a b ↔ GoverningOn M P L a b := by
  simpa only [GoverningOn, mechanicalResidual, thermalResidual, entropyResidual,
    sub_eq_zero] using stationary_iff_residuals M P L hab

/-- The thermal equation obtained from stationarity is the ACTUAL free-energy derivative. -/
theorem thermal_conjugacy_from_stationarity (M : Material) (P : Path) (L : Loads)
    {a b : ℝ} (hab : a < b) (hst : Stationary M P L a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    P.entropy t = -deriv (fun theta => freeEnergy M (P.x t) theta) (P.theta t) := by
  calc
    P.entropy t = entropyState M (P.x t) (P.theta t) :=
      ((pdel_basic_variational_theorem M P L hab).mp hst t ht).2.1
    _ = _ := entropy_is_negative_thermal_derivative M (P.x t) (P.theta t) (P.theta_pos t)

end PdelBasic
