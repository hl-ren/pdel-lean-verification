import Mathlib

/-!
# Concrete smooth Eulerian fields

Coordinate 0 is time; coordinates 1,2,3 are Euclidean space.  The scalar
algebra consists of actual C-infinity functions R^4 -> R.  Its derivatives
are mathlib Frechet derivatives, not an abstract differential operator.

The C-infinity assumption is stronger than necessary, but makes all residual
weighted tests admissible without introducing any equation of motion as data.
-/

noncomputable section
open scoped ContDiff Topology BigOperators
open Set MeasureTheory

namespace PdelEulerian

abbrev ST := Fin 4 → ℝ

def smoothScalars : Subalgebra ℝ (ST → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : ST => (0 : ℝ)); exact contDiff_const
  one_mem' := by change ContDiff ℝ ∞ (fun _ : ST => (1 : ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  mul_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).mul (show ContDiff ℝ ∞ g from hg)
  algebraMap_mem' := by
    intro c
    change ContDiff ℝ ∞ (fun _ : ST => c)
    exact contDiff_const

abbrev Scalar := ↥smoothScalars
instance : CoeFun Scalar (fun _ => ST → ℝ) := ⟨fun f => f.val⟩

@[ext] theorem scalar_ext {f g : Scalar} (h : ∀ p, f p = g p) : f = g :=
  Subtype.ext (funext h)

@[simp] theorem eval_zero (p : ST) : (0 : Scalar) p = 0 := rfl
@[simp] theorem eval_one (p : ST) : (1 : Scalar) p = 1 := rfl
@[simp] theorem eval_add (f g : Scalar) (p : ST) : (f + g) p = f p + g p := rfl
@[simp] theorem eval_neg (f : Scalar) (p : ST) : (-f) p = -f p := rfl
@[simp] theorem eval_sub (f g : Scalar) (p : ST) : (f - g) p = f p - g p := rfl
@[simp] theorem eval_mul (f g : Scalar) (p : ST) : (f * g) p = f p * g p := rfl
@[simp] theorem eval_pow (f : Scalar) (n : ℕ) (p : ST) : (f ^ n) p = f p ^ n := rfl

/-- Constant scalar field. -/
def C (c : ℝ) : Scalar := ⟨fun _ => c, by change ContDiff ℝ ∞ (fun _ : ST => c); exact contDiff_const⟩
@[simp] theorem eval_C (c : ℝ) (p : ST) : C c p = c := rfl
@[simp] theorem C_zero : C 0 = 0 := rfl
@[simp] theorem C_one : C 1 = 1 := rfl
@[simp] theorem C_add (a b : ℝ) : C (a+b) = C a+C b := rfl
@[simp] theorem C_mul (a b : ℝ) : C (a*b) = C a*C b := rfl
@[simp] theorem C_neg (a : ℝ) : C (-a) = -C a := rfl

namespace Scalar

theorem smooth (f : Scalar) : ContDiff ℝ ∞ (f : ST → ℝ) := f.property

theorem continuous (f : Scalar) : Continuous (f : ST → ℝ) := f.smooth.continuous

theorem differentiable (f : Scalar) : Differentiable ℝ (f : ST → ℝ) :=
  f.smooth.differentiable (by simp)

theorem hasFDerivAt (f : Scalar) (p : ST) :
    HasFDerivAt (f : ST → ℝ) (fderiv ℝ (f : ST → ℝ) p) p :=
  (f.differentiable p).hasFDerivAt

end Scalar

/-- The actual ith partial derivative of a smooth function. -/
def d (i : Fin 4) (f : Scalar) : Scalar :=
  ⟨fun p => fderiv ℝ (f : ST → ℝ) p (Pi.single i 1), by
    have hf : ContDiff ℝ ∞ (fderiv ℝ (f : ST → ℝ)) :=
      f.smooth.fderiv_right (by simp)
    exact hf.clm_apply contDiff_const⟩

@[simp] theorem d_apply (i : Fin 4) (f : Scalar) (p : ST) :
    d i f p = fderiv ℝ (f : ST → ℝ) p (Pi.single i 1) := rfl

@[simp] theorem d_C (i : Fin 4) (c : ℝ) : d i (C c) = 0 := by
  ext p
  simp [d, C]

@[simp] theorem d_zero (i : Fin 4) : d i (0 : Scalar) = 0 := d_C i 0
@[simp] theorem d_one (i : Fin 4) : d i (1 : Scalar) = 0 := d_C i 1

@[simp] theorem d_add (i : Fin 4) (f g : Scalar) : d i (f+g) = d i f+d i g := by
  ext p
  exact congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i 1))
    ((f.hasFDerivAt p).add (g.hasFDerivAt p)).fderiv

@[simp] theorem d_neg (i : Fin 4) (f : Scalar) : d i (-f) = -d i f := by
  ext p
  exact congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i 1))
    (f.hasFDerivAt p).neg.fderiv

@[simp] theorem d_sub (i : Fin 4) (f g : Scalar) : d i (f-g) = d i f-d i g := by
  simpa only [sub_eq_add_neg, d_add, d_neg]

@[simp] theorem d_mul (i : Fin 4) (f g : Scalar) :
    d i (f*g) = d i f*g+f*d i g := by
  ext p
  have h := congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i 1))
    ((f.hasFDerivAt p).mul (g.hasFDerivAt p)).fderiv
  simpa [d, mul_comm, add_comm] using h

@[simp] theorem d_sq (i : Fin 4) (f : Scalar) : d i (f^2) = C 2*f*d i f := by
  rw [pow_two, d_mul]
  ext p
  simp
  ring

/-- Mixed partials commute because the actual second Frechet derivative is symmetric. -/
theorem d_comm (i j : Fin 4) (f : Scalar) : d i (d j f) = d j (d i f) := by
  ext p
  have hs : ContDiff ℝ ∞ (fderiv ℝ (f : ST → ℝ)) :=
    f.smooth.fderiv_right (by simp)
  have hd := (hs.differentiable (by simp) p).hasFDerivAt
  have hi := hd.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ)) p)
  have hj := hd.clm_apply (hasFDerivAt_const (Pi.single j (1 : ℝ)) p)
  have hsym := second_derivative_symmetric (fun y => f.hasFDerivAt y) hd
    (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))
  change fderiv ℝ (fun q => (fderiv ℝ (f : ST → ℝ) q) (Pi.single j 1)) p
      (Pi.single i 1) =
    fderiv ℝ (fun q => (fderiv ℝ (f : ST → ℝ) q) (Pi.single i 1)) p
      (Pi.single j 1)
  rw [hj.fderiv, hi.fderiv]
  simpa using hsym

/-- Coordinates themselves are actual smooth linear functions. -/
def coordinate (i : Fin 4) : Scalar :=
  ⟨fun p => p i, by
    change ContDiff ℝ ∞ (ContinuousLinearMap.proj i : ST →L[ℝ] ℝ)
    exact ContinuousLinearMap.contDiff _⟩
@[simp] theorem coordinate_apply (i : Fin 4) (p : ST) : coordinate i p = p i := rfl
@[simp] theorem d_coordinate (i j : Fin 4) :
    d i (coordinate j) = C (if i=j then 1 else 0) := by
  ext p
  have h := congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i (1 : ℝ)))
    ((ContinuousLinearMap.proj j : ST →L[ℝ] ℝ).hasFDerivAt (x := p)).fderiv
  simpa only [d,coordinate,eval_C,ContinuousLinearMap.proj_apply,
    Pi.single_apply,eq_comm] using h

/-- Reciprocal of a nowhere-zero smooth field. -/
def reciprocal (f : Scalar) (hf : ∀ p, f p ≠ 0) : Scalar :=
  ⟨fun p => (f p)⁻¹, f.smooth.inv hf⟩
@[simp] theorem reciprocal_apply (f : Scalar) (hf) (p : ST) :
    reciprocal f hf p = (f p)⁻¹ := rfl

@[simp] theorem reciprocal_mul (f : Scalar) (hf : ∀ p, f p ≠ 0) :
    reciprocal f hf * f = 1 := by
  ext p
  simp [hf p]

@[simp] theorem mul_reciprocal (f : Scalar) (hf : ∀ p, f p ≠ 0) :
    f * reciprocal f hf = 1 := by
  rw [mul_comm, reciprocal_mul]

@[simp] theorem d_reciprocal (i : Fin 4) (f : Scalar) (hf : ∀ p, f p ≠ 0) :
    d i (reciprocal f hf) = -(reciprocal f hf)^2*d i f := by
  have h := congrArg (d i) (reciprocal_mul f hf)
  rw [d_mul, d_one] at h
  ext p
  have hp := congrArg (fun k : Scalar => k p) h
  simp only [eval_add, eval_mul, eval_zero] at hp
  simp only [eval_mul, eval_neg, eval_pow, reciprocal_apply]
  have hp0 := hf p
  field_simp [hp0] at hp ⊢
  nlinarith

/-- The real logarithm, defined only using a nowhere-zero argument. -/
def slog (f : Scalar) (hf : ∀ p, f p ≠ 0) : Scalar :=
  ⟨fun p => Real.log (f p), f.smooth.log hf⟩
@[simp] theorem slog_apply (f : Scalar) (hf) (p : ST) :
    slog f hf p = Real.log (f p) := rfl

@[simp] theorem d_slog (i : Fin 4) (f : Scalar) (hf : ∀ p, f p ≠ 0) :
    d i (slog f hf) = reciprocal f hf*d i f := by
  ext p
  have h := congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i 1))
    ((f.hasFDerivAt p).log (hf p)).fderiv
  simpa [d, reciprocal] using h

/-- Elementary smooth operations used by the nonzero-current witness. -/
def sexp (f : Scalar) : Scalar := ⟨fun p => Real.exp (f p),f.smooth.exp⟩
def ssin (f : Scalar) : Scalar := ⟨fun p => Real.sin (f p),f.smooth.sin⟩
def scos (f : Scalar) : Scalar := ⟨fun p => Real.cos (f p),f.smooth.cos⟩
@[simp] theorem sexp_apply (f : Scalar) (p : ST) : sexp f p=Real.exp (f p) := rfl
@[simp] theorem ssin_apply (f : Scalar) (p : ST) : ssin f p=Real.sin (f p) := rfl
@[simp] theorem scos_apply (f : Scalar) (p : ST) : scos f p=Real.cos (f p) := rfl

@[simp] theorem d_sexp (i : Fin 4) (f : Scalar) : d i (sexp f)=sexp f*d i f := by
  ext p
  have h := congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i 1))
    (f.hasFDerivAt p).exp.fderiv
  simpa [d,sexp] using h

@[simp] theorem d_ssin (i : Fin 4) (f : Scalar) : d i (ssin f)=scos f*d i f := by
  ext p
  have h := congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i 1))
    (f.hasFDerivAt p).sin.fderiv
  simpa [d,scos] using h

@[simp] theorem d_scos (i : Fin 4) (f : Scalar) : d i (scos f)=-ssin f*d i f := by
  ext p
  have h := congrArg (fun L : ST →L[ℝ] ℝ => L (Pi.single i 1))
    (f.hasFDerivAt p).cos.fderiv
  change fderiv ℝ (fun q => Real.cos (f q)) p (Pi.single i 1) =
    -Real.sin (f p) * fderiv ℝ (f : ST → ℝ) p (Pi.single i 1)
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h

theorem ssin_sq_add_scos_sq (f : Scalar) : ssin f^2+scos f^2=1 := by
  ext p
  exact Real.sin_sq_add_cos_sq (f p)

/-- Vanishing on a neighborhood implies vanishing partial derivatives there. -/
theorem d_eq_zero_on_open {U : Set ST} (hU : IsOpen U) (f : Scalar)
    (hf : ∀ p ∈ U, f p = 0) {p : ST} (hp : p ∈ U) (i : Fin 4) : d i f p = 0 := by
  have he : (f : ST → ℝ) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) :=
    Filter.mem_of_superset (hU.mem_nhds hp) (fun q hq => hf q hq)
  change fderiv ℝ (f : ST → ℝ) p (Pi.single i 1) = 0
  rw [he.fderiv_eq]
  simp

end PdelEulerian
