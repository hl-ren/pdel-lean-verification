import PdelBridge.Tensor
import PdelEulerian.Equations

noncomputable section
open PdelEulerian
namespace PdelBridge

theorem positive_pairing_norm_positive (A J : Vector) (hpos : ∀ p, 0 < dot A J p) :
    ∀ p, 0 < normSq J p := by
  intro p
  exact PdelMHD.normSq_pos (toV3 (valueV J p))
    (PdelMHD.current_nonzero (toV3 (valueV A p)) (toV3 (valueV J p)) (hpos p))

/-- No independent denominator assumptions are necessary when A·J > 0. -/
def positiveSeed (ell : ℝ) (A J : Vector) (hpos : ∀ p, 0 < dot A J p) : Tensor :=
  seedTensor ell A J (fun p => ne_of_gt (hpos p))
    (fun p => ne_of_gt (positive_pairing_norm_positive A J hpos p))

/-- A constitutive identification connects Layer 1 to the actual Layer-3
Ohm/Joule consequence of integral stationarity. No Ohm equation is assumed. -/
theorem stationary_seed_joule (ell : ℝ) (A : Vector)
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hpos : ∀ p, 0 < dot A P.current p)
    (heta : K.eta = positiveSeed ell A P.current hpos)
    (hs : Stationary Q G K P F t0) {p : ST} (hp : p ∈ Q.closed) :
    P.joulePower K p = ell * dot A P.current p := by
  have hOhm := ((eulerian_pdel_variational_theorem Q G K P F t0).mp hs p hp).2.1
  rw [P.joule_on_ohm K hOhm, heta]
  exact seed_current_power ell A P.current _ _ p

theorem stationary_seed_joule_positive (ell : ℝ) (hell : 0 < ell) (A : Vector)
    (Q : Box) (G : Gas) (K : Transport) (P : Fields)
    (F : MaterialChart P.velocity) (t0 : ℝ)
    (hpos : ∀ p, 0 < dot A P.current p)
    (heta : K.eta = positiveSeed ell A P.current hpos)
    (hs : Stationary Q G K P F t0) {p : ST} (hp : p ∈ Q.closed) :
    0 < P.joulePower K p := by
  rw [stationary_seed_joule ell A Q G K P F t0 hpos heta hs hp]
  exact mul_pos hell (hpos p)

def unitVector : Vector := ![1, 0, 0]

theorem unit_pairing_positive : ∀ p : ST, 0 < dot unitVector unitVector p := by
  intro p
  change 0 < (1 : ℝ)*1+0*0+0*0
  norm_num

/-- An explicit nonempty family with a smooth inverse, realizing the Layer-1
seed as a full Layer-3 Transport. Its eigenvalues are ell,1,1. -/
def seedTransport (ell : ℝ) (hell : 0 < ell) : Transport where
  eta := positiveSeed ell unitVector unitVector unit_pairing_positive
  sigma := fun i j => if i = j then (if i = 0 then C ell⁻¹ else 1) else 0
  inverse := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [positiveSeed, seedTensor, unitVector, dot, normSq]
    all_goals
      apply scalar_ext
      intro p
      simp [ne_of_gt hell]
  eta_symmetric := seed_symmetric ell unitVector unitVector _ _
  sigma_symmetric := by intro i j; by_cases h : i = j <;> simp_all [eq_comm]
  eta_pos := by
    intro p z hz
    exact seed_positive_definite ell unitVector unitVector _ _ hell unit_pairing_positive p z hz
  sigma_nonneg := by
    intro p z
    change 0 ≤ z 0 * (ell⁻¹ * z 0 + 0*z 1 + 0*z 2) +
      z 1 * (0*z 0 + 1*z 1 + 0*z 2) + z 2 * (0*z 0 + 0*z 1 + 1*z 2)
    have h := mul_nonneg (inv_nonneg.mpr hell.le) (sq_nonneg (z 0))
    nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
  bulk := 0
  thermal := 0
  bulk_nonneg := fun _ => le_rfl
  thermal_nonneg := fun _ => le_rfl

theorem seed_transport_realizes_tensor (ell : ℝ) (hell : 0 < ell) :
    (seedTransport ell hell).eta = positiveSeed ell unitVector unitVector unit_pairing_positive := rfl

end PdelBridge
