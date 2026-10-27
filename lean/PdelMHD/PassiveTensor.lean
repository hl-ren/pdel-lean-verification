import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Pointwise passive tensor realization in real three-dimensional space

Source target: Lemma `lem:tensor` and equation `eq:tensor` in the manuscript.
This file contains a proposed complete proof of the **finite-dimensional**
lemma. No curl, topology, transport or uniform-on-a-domain assertion is hidden
in its hypotheses. Compilation status is recorded separately in BUILD_STATUS.md.
-/

noncomputable section

namespace PdelMHD

@[ext] structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

def zeroV : V3 := ⟨0, 0, 0⟩
def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z
def normSq (v : V3) : ℝ := dot v v

def cross (u v : V3) : V3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

def scale (a : ℝ) (v : V3) : V3 := ⟨a*v.x, a*v.y, a*v.z⟩

/-- The linear action of M = ell A Aᵀ/(A·J) + I - J Jᵀ/(J·J). -/
def tensorAction (ell : ℝ) (A J v : V3) : V3 :=
  ⟨ell * A.x * dot A v / dot A J + v.x - J.x * dot J v / normSq J,
   ell * A.y * dot A v / dot A J + v.y - J.y * dot J v / normSq J,
   ell * A.z * dot A v / dot A J + v.z - J.z * dot J v / normSq J⟩

theorem dot_comm (u v : V3) : dot u v = dot v u := by
  dsimp [dot]
  ring

theorem normSq_nonneg (v : V3) : 0 ≤ normSq v := by
  dsimp [normSq, dot]
  nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]

theorem normSq_eq_zero (v : V3) : normSq v = 0 ↔ v = zeroV := by
  constructor
  · intro h
    have hx : v.x = 0 := by
      dsimp [normSq, dot] at h
      nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    have hy : v.y = 0 := by
      dsimp [normSq, dot] at h
      nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    have hz : v.z = 0 := by
      dsimp [normSq, dot] at h
      nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    apply V3.ext
    · simpa [zeroV] using hx
    · simpa [zeroV] using hy
    · simpa [zeroV] using hz
  · intro h
    simp [h, normSq, dot, zeroV]

theorem normSq_pos (v : V3) (h : v ≠ zeroV) : 0 < normSq v := by
  by_contra hn
  have he : normSq v = 0 :=
    le_antisymm (le_of_not_gt hn) (normSq_nonneg v)
  exact h ((normSq_eq_zero v).mp he)

theorem current_nonzero (A J : V3) (hg : 0 < dot A J) : J ≠ zeroV := by
  intro h
  simpa [h, zeroV, dot] using hg

theorem lagrange_identity (u v : V3) :
    normSq (cross u v) = normSq u * normSq v - (dot u v)^2 := by
  dsimp [normSq, dot, cross]
  ring

theorem triple_x (A J v : V3) :
    dot A J * v.x = dot A v * J.x - (cross A (cross J v)).x := by
  dsimp [dot, cross]
  ring

theorem triple_y (A J v : V3) :
    dot A J * v.y = dot A v * J.y - (cross A (cross J v)).y := by
  dsimp [dot, cross]
  ring

theorem triple_z (A J v : V3) :
    dot A J * v.z = dot A v * J.z - (cross A (cross J v)).z := by
  dsimp [dot, cross]
  ring

/-- The two kernels in the sum-of-squares representation intersect only at 0. -/
theorem zero_of_dot_cross (A J v : V3) (hg : dot A J ≠ 0)
    (ha : dot A v = 0) (hc : cross J v = zeroV) : v = zeroV := by
  have hx : dot A J * v.x = 0 := by
    rw [triple_x, ha, hc]
    simp [cross, zeroV]
  have hy : dot A J * v.y = 0 := by
    rw [triple_y, ha, hc]
    simp [cross, zeroV]
  have hz : dot A J * v.z = 0 := by
    rw [triple_z, ha, hc]
    simp [cross, zeroV]
  apply V3.ext
  · simpa [zeroV] using (mul_eq_zero.mp hx).resolve_left hg
  · simpa [zeroV] using (mul_eq_zero.mp hy).resolve_left hg
  · simpa [zeroV] using (mul_eq_zero.mp hz).resolve_left hg

/-- Exact current mapping, with the denominators stated explicitly. -/
theorem tensor_maps_current (ell : ℝ) (A J : V3)
    (hg : dot A J ≠ 0) (hj : normSq J ≠ 0) :
    tensorAction ell A J J = scale ell A := by
  have hg' : A.x*J.x + A.y*J.y + A.z*J.z ≠ 0 := hg
  have hj' : J.x*J.x + J.y*J.y + J.z*J.z ≠ 0 := hj
  apply V3.ext <;> dsimp [tensorAction, scale, dot, normSq] <;>
    field_simp [hg', hj'] <;> ring

theorem tensor_bilinear_symmetric (ell : ℝ) (A J u v : V3)
    (hg : dot A J ≠ 0) (hj : normSq J ≠ 0) :
    dot u (tensorAction ell A J v) = dot v (tensorAction ell A J u) := by
  have hg' : A.x*J.x + A.y*J.y + A.z*J.z ≠ 0 := hg
  have hj' : J.x*J.x + J.y*J.y + J.z*J.z ≠ 0 := hj
  dsimp [tensorAction, dot, normSq]
  field_simp [hg', hj'] <;> ring

/-- Direct Cartesian sum of squares, not an assumption of positive definiteness. -/
theorem tensor_quadratic_sos (ell : ℝ) (A J v : V3)
    (hg : dot A J ≠ 0) (hj : normSq J ≠ 0) :
    dot v (tensorAction ell A J v) =
      ell * (dot A v)^2 / dot A J + normSq (cross J v) / normSq J := by
  have hg' : A.x*J.x + A.y*J.y + A.z*J.z ≠ 0 := hg
  have hj' : J.x*J.x + J.y*J.y + J.z*J.z ≠ 0 := hj
  dsimp [tensorAction, dot, normSq, cross]
  field_simp [hg', hj'] <;> ring

/-- The full pointwise SPD conclusion, for arbitrary real A,J with A·J>0. -/
theorem tensor_positive_definite (ell : ℝ) (A J : V3)
    (hell : 0 < ell) (hg : 0 < dot A J) :
    ∀ v : V3, v ≠ zeroV → 0 < dot v (tensorAction ell A J v) := by
  intro v hv
  have hj : 0 < normSq J := normSq_pos J (current_nonzero A J hg)
  rw [tensor_quadratic_sos ell A J v (ne_of_gt hg) (ne_of_gt hj)]
  have h1 : 0 ≤ ell * (dot A v)^2 / dot A J :=
    div_nonneg (mul_nonneg (le_of_lt hell) (sq_nonneg _)) (le_of_lt hg)
  have h2 : 0 ≤ normSq (cross J v) / normSq J :=
    div_nonneg (normSq_nonneg _) (le_of_lt hj)
  by_contra hn
  have hsum : ell * (dot A v)^2 / dot A J + normSq (cross J v) / normSq J ≤ 0 :=
    le_of_not_gt hn
  have h1z : ell * (dot A v)^2 / dot A J = 0 := by linarith
  have h2z : normSq (cross J v) / normSq J = 0 := by linarith
  have hn1 : ell * (dot A v)^2 = 0 := by
    simpa using (div_eq_iff (ne_of_gt hg)).mp h1z
  have hn2 : normSq (cross J v) = 0 := by
    simpa using (div_eq_iff (ne_of_gt hj)).mp h2z
  have hasq : (dot A v)^2 = 0 :=
    (mul_eq_zero.mp hn1).resolve_left (ne_of_gt hell)
  have ha : dot A v = 0 := by nlinarith
  have hc : cross J v = zeroV := (normSq_eq_zero _).mp hn2
  exact hv (zero_of_dot_cross A J v (ne_of_gt hg) ha hc)

/-- A useful power identity, once the pointwise operator is fixed. -/
theorem current_power (ell : ℝ) (A J : V3)
    (hg : dot A J ≠ 0) (hj : normSq J ≠ 0) :
    dot J (tensorAction ell A J J) = ell * dot A J := by
  rw [tensor_maps_current ell A J hg hj]
  dsimp [dot, scale]
  ring

end PdelMHD
