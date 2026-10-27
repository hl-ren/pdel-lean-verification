import PdelEulerian

noncomputable section
open PdelEulerian
namespace PdelRevision3

/-- A field specialization, not an assumption of any fluid balance equation. -/
def nonmagneticFields (S : ThermalState) (v : Vector) : Fields := ⟨S, v, 0⟩

theorem curl_zero_vector : curl (0 : Vector) = 0 := by
  funext i
  fin_cases i <;> simp [curl, dx]

theorem dt_zero_vector : dtV (0 : Vector) = 0 := by
  funext i
  simp [dtV, dt]

theorem cross_zero_vector (v : Vector) : cross v 0 = 0 := by
  funext i
  fin_cases i <;> simp [cross]

theorem matvec_zero_vector (M : Tensor) : matvec M 0 = 0 := by
  funext i
  simp [matvec]

theorem nonmagnetic_magnetic (S : ThermalState) (v : Vector) :
    (nonmagneticFields S v).magnetic = 0 := curl_zero_vector

theorem nonmagnetic_current (S : ThermalState) (v : Vector) :
    (nonmagneticFields S v).current = 0 := by
  rw [Fields.current, nonmagnetic_magnetic, curl_zero_vector]

theorem nonmagnetic_relative_rate (S : ThermalState) (v : Vector) :
    (nonmagneticFields S v).relativeRate = 0 := by
  rw [Fields.relativeRate, nonmagnetic_magnetic, cross_zero_vector]
  change dtV (0 : Vector) - 0 = 0
  rw [dt_zero_vector, sub_zero]

theorem nonmagnetic_resistance (K : Transport) (S : ThermalState) (v : Vector) :
    (nonmagneticFields S v).resistance K = 0 := by
  rw [Fields.resistance, nonmagnetic_relative_rate, matvec_zero_vector]

theorem nonmagnetic_joule (K : Transport) (S : ThermalState) (v : Vector) :
    (nonmagneticFields S v).joulePower K = 0 := by
  rw [Fields.joulePower, nonmagnetic_relative_rate]
  simp [dot]

theorem nonmagnetic_ohm (K : Transport) (S : ThermalState) (v : Vector) :
    (nonmagneticFields S v).ohmDefect K = 0 := by
  rw [Fields.ohmDefect, nonmagnetic_magnetic, nonmagnetic_current,
    cross_zero_vector, matvec_zero_vector]
  change -dtV (0 : Vector) + 0 - 0 = 0
  rw [dt_zero_vector]
  simp

/-- Keep all three fluid tests independent; the potential test may still be arbitrary. -/
def withoutPotentialTest (V : Test) : Test :=
  ⟨V.xi, 0, V.temperature, V.entropySelector⟩

theorem nonmagnetic_first_variation (Q : Box) (G : Gas) (K : Transport)
    (S : ThermalState) (v : Vector) (F : MaterialChart v) (t0 : ℝ) (V : Test) :
    firstVariation Q G K (nonmagneticFields S v) F t0 V =
      firstVariation Q G K (nonmagneticFields S v) F t0 (withoutPotentialTest V) := by
  rw [firstVariation_raw, firstVariation_raw]
  congr 1
  simp only [rawVariation, nonmagnetic_magnetic, nonmagnetic_resistance, dot,
    Pi.zero_apply, zero_mul, zero_add, sub_zero,
    Test.dv, Test.drho, Test.dtemp, Test.ds, withoutPotentialTest]

/-- The three nonmagnetic equations are outputs of stationarity. -/
def FluidEquationsOn (Q : Box) (G : Gas) (K : Transport)
    (S : ThermalState) (v : Vector) : Prop :=
  ∀ p ∈ Q.closed,
    (∀ i, (scale S.rho (materialV v v) + grad (S.pressure G) -
      divTensor ((nonmagneticFields S v).viscousStress K)) i p = 0) ∧
    S.entropy p = -S.phiTemp G p ∧
    (S.temp * conservative v S.entropy + div ((nonmagneticFields S v).heatFlux K) -
      (nonmagneticFields S v).viscousPower K) p = 0

/-- Revision3 eq:revieweulerbalances, with the original independent Test space
and fixed-box boundary class. Mass is a kinematic admissibility premise. -/
theorem nonmagnetic_stationarity_iff (Q : Box) (G : Gas) (K : Transport)
    (S : ThermalState) (v : Vector) (F : MaterialChart v) (t0 : ℝ)
    (hmass : MassAdmissible Q (nonmagneticFields S v)) :
    Stationary Q G K (nonmagneticFields S v) F t0 ↔ FluidEquationsOn Q G K S v := by
  rw [eulerian_pdel_mhd_theorem Q G K (nonmagneticFields S v) F t0 hmass]
  constructor
  · intro h p hp
    rcases h p hp with ⟨_, hm, _, hT, hS⟩
    refine ⟨?_, hT, ?_⟩
    · simpa only [Fields.physicalMomentum, nonmagnetic_magnetic, cross_zero_vector,
        sub_zero] using hm
    · simpa only [Fields.physicalEntropy, Fields.physicalThermalPower,
        nonmagnetic_current, dot, Pi.zero_apply, zero_mul, zero_add] using hS
  · intro h p hp
    rcases h p hp with ⟨hm, hT, hS⟩
    refine ⟨hmass p hp, ?_, ?_, hT, ?_⟩
    · simpa only [Fields.physicalMomentum, nonmagnetic_magnetic, cross_zero_vector,
        sub_zero] using hm
    · intro i
      rw [nonmagnetic_ohm]
      rfl
    · simpa only [Fields.physicalEntropy, Fields.physicalThermalPower,
        nonmagnetic_current, dot, Pi.zero_apply, zero_mul, zero_add] using hS

end PdelRevision3
