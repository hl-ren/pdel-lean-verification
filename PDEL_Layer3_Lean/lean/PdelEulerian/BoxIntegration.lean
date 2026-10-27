import PdelEulerian.FirstVariation

/-!
# Actual spacetime integration and localization

The measure is four-dimensional Euclidean volume on a nondegenerate Cartesian
box.  BoundaryFlux is a sum of eight genuine three-dimensional face integrals.
No integration-by-parts or fundamental-lemma assumption is introduced.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology
namespace PdelEulerian

structure Box where
  lo : ST
  hi : ST
  strict : ∀ i, lo i < hi i

namespace Box

def closed (Q : Box) : Set ST := Set.Icc Q.lo Q.hi

/-- Coordinatewise open rectangle. `Set.Ioo lo hi` on the product partial order
would be the WRONG set here. -/
def interior (Q : Box) : Set ST := Set.univ.pi (fun i => Set.Ioo (Q.lo i) (Q.hi i))

def integrate (Q : Box) (f : ST → ℝ) : ℝ := ∫ p in Q.closed, f p

def integral (Q : Box) (f : Scalar) : ℝ := Q.integrate f

def boundaryFlux (Q : Box) (F : Vector4) : ℝ :=
  ∑ i : Fin 4,
    ((∫ y in Set.Icc (Q.lo ∘ i.succAbove) (Q.hi ∘ i.succAbove),
        F i (i.insertNth (Q.hi i) y)) -
     (∫ y in Set.Icc (Q.lo ∘ i.succAbove) (Q.hi ∘ i.succAbove),
        F i (i.insertNth (Q.lo i) y)))

/-- Vanishing on all face hyperplanes is a convenient, sufficiently rich test class.
It is a condition on tests, not on physical fields. -/
def VanishesOnFaces (Q : Box) (f : Scalar) : Prop :=
  ∀ (i : Fin 4) (p : ST), p i=Q.lo i ∨ p i=Q.hi i → f p=0

theorem le (Q : Box) : Q.lo ≤ Q.hi := fun i => (Q.strict i).le

theorem mem_interior (Q : Box) (p : ST) :
    p ∈ Q.interior ↔ ∀ i, Q.lo i < p i ∧ p i < Q.hi i := by
  simp [interior, Set.mem_pi]

theorem mem_closed (Q : Box) (p : ST) :
    p ∈ Q.closed ↔ ∀ i, Q.lo i ≤ p i ∧ p i ≤ Q.hi i := by
  simp [closed, Set.mem_Icc, Pi.le_def, forall_and]

theorem interior_subset (Q : Box) : Q.interior ⊆ Q.closed := by
  intro p hp
  rw [Q.mem_interior] at hp
  rw [Q.mem_closed]
  exact fun i => ⟨(hp i).1.le, (hp i).2.le⟩

theorem interior_open (Q : Box) : IsOpen Q.interior := by
  exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)

theorem closure_interior (Q : Box) : closure Q.interior = Q.closed := by
  rw [interior, closure_pi_set]
  have hc : (fun i : Fin 4 => closure (Set.Ioo (Q.lo i) (Q.hi i))) =
      (fun i => Set.Icc (Q.lo i) (Q.hi i)) := by
    funext i
    exact closure_Ioo (Q.strict i).ne
  rw [hc]
  ext p
  simp [closed, Set.mem_pi, Set.mem_Icc, Pi.le_def, forall_and]

theorem integrable (Q : Box) (f : Scalar) : IntegrableOn (f : ST → ℝ) Q.closed :=
  f.continuous.integrableOn_Icc

@[simp] theorem integral_zero (Q : Box) : Q.integral 0 = 0 := by
  simp [integral, integrate]

theorem integral_add (Q : Box) (f g : Scalar) :
    Q.integral (f+g) = Q.integral f+Q.integral g := by
  exact MeasureTheory.integral_add (Q.integrable f) (Q.integrable g)

theorem integral_neg (Q : Box) (f : Scalar) : Q.integral (-f) = -Q.integral f := by
  exact MeasureTheory.integral_neg (f : ST → ℝ)

theorem integral_sub (Q : Box) (f g : Scalar) :
    Q.integral (f-g) = Q.integral f-Q.integral g := by
  exact MeasureTheory.integral_sub (Q.integrable f) (Q.integrable g)

theorem integral_congr (Q : Box) {f g : Scalar}
    (h : ∀ p ∈ Q.closed, f p=g p) : Q.integral f=Q.integral g := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  exact h

/-- The actual divergence theorem on a 3+1-dimensional Euclidean box. -/
theorem integral_divergence (Q : Box) (F : Vector4) :
    Q.integral (div4 F) = Q.boundaryFlux F := by
  have hsum : (fun p => ∑ i : Fin 4,
      fderiv ℝ (F i : ST → ℝ) p (Pi.single i 1)) = (div4 F : ST → ℝ) := by
    funext p
    simp [div4, Fin.sum_univ_succ, d_apply, add_assoc]
  have hint : IntegrableOn
      (fun p => ∑ i : Fin 4, fderiv ℝ (F i : ST → ℝ) p (Pi.single i 1))
      (Set.Icc Q.lo Q.hi) := by
    rw [hsum]
    exact Q.integrable (div4 F)
  have h := MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable'
    Q.lo Q.hi Q.le (fun i => (F i : ST → ℝ))
    (fun i p => fderiv ℝ (F i : ST → ℝ) p)
    (∅ : Set ST) Set.countable_empty
    (fun i => (F i).continuous.continuousOn)
    (fun p _ i => (F i).hasFDerivAt p) hint
  simpa only [hsum, integral, integrate, closed, boundaryFlux] using h

theorem boundaryFlux_zero (Q : Box) (F : Vector4)
    (hF : ∀ i, Q.VanishesOnFaces (F i)) : Q.boundaryFlux F=0 := by
  unfold boundaryFlux
  apply Finset.sum_eq_zero
  intro i _
  have hh : (fun y : Fin 3 → ℝ => F i (i.insertNth (Q.hi i) y)) = fun _ => 0 := by
    funext y
    apply hF i i _
    exact Or.inr (by simp)
  have hl : (fun y : Fin 3 → ℝ => F i (i.insertNth (Q.lo i) y)) = fun _ => 0 := by
    funext y
    apply hF i i _
    exact Or.inl (by simp)
  rw [hh, hl]
  simp

@[simp] theorem zero_vanishes (Q : Box) : Q.VanishesOnFaces 0 := by
  intro i p hp
  rfl

theorem mul_vanishes (Q : Box) {f : Scalar} (hf : Q.VanishesOnFaces f)
    (g : Scalar) : Q.VanishesOnFaces (f*g) := by
  intro i p hp
  simp [hf i p hp]

/-- Explicit polynomial, positive in the open box and zero on every face. -/
def weightFactor (Q : Box) (i : Fin 4) : Scalar :=
  (coordinate i-C (Q.lo i))^2*(C (Q.hi i)-coordinate i)^2

def weight (Q : Box) : Scalar :=
  Q.weightFactor 0*Q.weightFactor 1*Q.weightFactor 2*Q.weightFactor 3

theorem weight_nonnegative (Q : Box) (p : ST) : 0 ≤ Q.weight p := by
  simp only [weight, weightFactor, eval_mul, eval_pow, eval_sub, coordinate_apply, eval_C]
  positivity

theorem weight_positive (Q : Box) {p : ST} (hp : p ∈ Q.interior) :
    0 < Q.weight p := by
  have h := (Q.mem_interior p).mp hp
  have hf : ∀ i : Fin 4, 0 < Q.weightFactor i p := by
    intro i
    simp only [weightFactor, eval_mul, eval_pow, eval_sub, coordinate_apply, eval_C]
    exact mul_pos (sq_pos_of_pos (sub_pos.mpr (h i).1))
      (sq_pos_of_pos (sub_pos.mpr (h i).2))
  exact mul_pos (mul_pos (mul_pos (hf 0) (hf 1)) (hf 2)) (hf 3)

theorem weight_vanishes (Q : Box) : Q.VanishesOnFaces Q.weight := by
  intro i p hp
  have hz : Q.weightFactor i p = 0 := by
    simp only [weightFactor, eval_mul, eval_pow, eval_sub, coordinate_apply, eval_C]
    rcases hp with hp | hp <;> rw [hp] <;> simp
  fin_cases i <;> simp_all [weight]

/-- Fundamental-lemma argument proved using an actual nonnegative integral.
It is NOT an assumption equating weak stationarity with a residual. -/
theorem weighted_square_localization (Q : Box) (f : Scalar)
    (h : Q.integral (Q.weight*f^2)=0) : ∀ p ∈ Q.closed, f p=0 := by
  let g : Scalar := Q.weight*f^2
  have hnn : ∀ p, 0 ≤ g p := by
    intro p
    exact mul_nonneg (Q.weight_nonnegative p) (sq_nonneg (f p))
  have hi : Integrable (g : ST → ℝ) (volume.restrict Q.closed) := Q.integrable g
  have hz : (g : ST → ℝ) =ᵐ[volume.restrict Q.closed] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg hnn hi).mp h
  have hzo : (g : ST → ℝ) =ᵐ[volume.restrict Q.interior] 0 :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Q.interior_subset hz
  have hpoint : Set.EqOn (g : ST → ℝ) (fun _ => 0) Q.interior :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hzo Q.interior_open
      g.continuous.continuousOn continuous_const.continuousOn
  have hf : Set.EqOn (f : ST → ℝ) (fun _ => 0) Q.interior := by
    intro p hp
    have hg : Q.weight p*(f p)^2=0 := hpoint hp
    have hw : Q.weight p≠0 := ne_of_gt (Q.weight_positive hp)
    have hsq : (f p)^2=0 := (mul_eq_zero.mp hg).resolve_left hw
    exact sq_eq_zero_iff.mp hsq
  have hc := hf.closure f.continuous continuous_const
  rw [Q.closure_interior] at hc
  exact hc

end Box
end PdelEulerian
