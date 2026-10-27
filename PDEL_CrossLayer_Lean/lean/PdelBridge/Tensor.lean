import PdelBridge.Vectors

noncomputable section
open PdelEulerian
namespace PdelBridge

/-- A smooth field of the exact passive tensors constructed in Layer 1.
Nonzero denominators are explicit construction data; positivity is proved. -/
def seedTensor (ell : ℝ) (A J : Vector)
    (hg : ∀ p, dot A J p ≠ 0) (hj : ∀ p, normSq J p ≠ 0) : Tensor :=
  fun i j => C ell * A i * A j * reciprocal (dot A J) hg +
    (if i = j then 1 else 0) - J i * J j * reciprocal (normSq J) hj

theorem seed_action (ell : ℝ) (A J w : Vector)
    (hg : ∀ p, dot A J p ≠ 0) (hj : ∀ p, normSq J p ≠ 0) (p : ST) :
    toV3 (valueV (matvec (seedTensor ell A J hg hj) w) p) =
      PdelMHD.tensorAction ell (toV3 (valueV A p)) (toV3 (valueV J p))
        (toV3 (valueV w p)) := by
  apply PdelMHD.V3.ext <;>
    simp [toV3, valueV, matvec, seedTensor, PdelMHD.tensorAction,
      PdelMHD.dot, PdelMHD.normSq, dot, normSq, div_eq_mul_inv] <;> ring

theorem seed_symmetric (ell : ℝ) (A J : Vector)
    (hg : ∀ p, dot A J p ≠ 0) (hj : ∀ p, normSq J p ≠ 0) :
    ∀ i j, seedTensor ell A J hg hj i j = seedTensor ell A J hg hj j i := by
  intro i j
  simp only [seedTensor, eq_comm]
  ring

/-- Layer 1 supplies positive definiteness for the constructed smooth tensor.
No smooth inverse, uniform ellipticity, or governing equation is assumed here. -/
theorem seed_positive_definite (ell : ℝ) (A J : Vector)
    (hg : ∀ p, dot A J p ≠ 0) (hj : ∀ p, normSq J p ≠ 0)
    (hell : 0 < ell) (hpos : ∀ p, 0 < dot A J p)
    (p : ST) (z : RVector) (hz : z ≠ 0) :
    0 < rdot z (fun i => seedTensor ell A J hg hj i 0 p * z 0 +
      seedTensor ell A J hg hj i 1 p * z 1 + seedTensor ell A J hg hj i 2 p * z 2) := by
  let w : Vector := fun i => C (z i)
  have h := PdelMHD.tensor_positive_definite ell (toV3 (valueV A p))
    (toV3 (valueV J p)) hell (hpos p) (toV3 z)
    (fun he => hz ((toV3_zero_iff z).mp he))
  change 0 < PdelMHD.dot (toV3 (valueV w p))
    (PdelMHD.tensorAction ell (toV3 (valueV A p)) (toV3 (valueV J p)) (toV3 (valueV w p))) at h
  rw [← seed_action ell A J w hg hj p] at h
  exact h

theorem seed_maps_current (ell : ℝ) (A J : Vector)
    (hg : ∀ p, dot A J p ≠ 0) (hj : ∀ p, normSq J p ≠ 0) :
    matvec (seedTensor ell A J hg hj) J = scale (C ell) A := by
  funext i
  apply scalar_ext
  intro p
  have h := PdelMHD.tensor_maps_current ell (toV3 (valueV A p))
    (toV3 (valueV J p)) (hg p) (hj p)
  rw [← seed_action ell A J J hg hj p] at h
  have hv := congrArg (fun v => fromV3 v i) h
  fin_cases i <;> simpa [PdelMHD.scale, fromV3, toV3, valueV, scale] using hv

theorem seed_current_power (ell : ℝ) (A J : Vector)
    (hg : ∀ p, dot A J p ≠ 0) (hj : ∀ p, normSq J p ≠ 0) (p : ST) :
    dot J (matvec (seedTensor ell A J hg hj) J) p = ell * dot A J p := by
  have h := PdelMHD.current_power ell (toV3 (valueV A p))
    (toV3 (valueV J p)) (hg p) (hj p)
  rw [← seed_action ell A J J hg hj p] at h
  simpa only [dot_evaluation] using h

end PdelBridge
