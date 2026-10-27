import PdelEulerian.Smooth

noncomputable section
open scoped BigOperators
namespace PdelEulerian

abbrev Vector := Fin 3 → Scalar
abbrev Tensor := Fin 3 → Fin 3 → Scalar
abbrev Vector4 := Fin 4 → Scalar

def dt (f : Scalar) : Scalar := d 0 f
def dx (i : Fin 3) (f : Scalar) : Scalar := d i.succ f

@[simp] theorem dt_C (c : ℝ) : dt (C c)=0 := d_C 0 c
@[simp] theorem dt_zero : dt (0 : Scalar)=0 := d_zero 0
@[simp] theorem dt_one : dt (1 : Scalar)=0 := d_one 0
@[simp] theorem dt_add (f g : Scalar) : dt (f+g)=dt f+dt g := d_add 0 f g
@[simp] theorem dt_sub (f g : Scalar) : dt (f-g)=dt f-dt g := d_sub 0 f g
@[simp] theorem dt_neg (f : Scalar) : dt (-f)=-dt f := d_neg 0 f
@[simp] theorem dt_mul (f g : Scalar) : dt (f*g)=dt f*g+f*dt g := d_mul 0 f g
@[simp] theorem dt_sq (f : Scalar) : dt (f^2)=C 2*f*dt f := d_sq 0 f
@[simp] theorem dx_C (i : Fin 3) (c : ℝ) : dx i (C c)=0 := d_C i.succ c
@[simp] theorem dx_zero (i : Fin 3) : dx i (0 : Scalar)=0 := d_zero i.succ
@[simp] theorem dx_one (i : Fin 3) : dx i (1 : Scalar)=0 := d_one i.succ
@[simp] theorem dx_add (i : Fin 3) (f g : Scalar) : dx i (f+g)=dx i f+dx i g := d_add i.succ f g
@[simp] theorem dx_sub (i : Fin 3) (f g : Scalar) : dx i (f-g)=dx i f-dx i g := d_sub i.succ f g
@[simp] theorem dx_neg (i : Fin 3) (f : Scalar) : dx i (-f)=-dx i f := d_neg i.succ f
@[simp] theorem dx_mul (i : Fin 3) (f g : Scalar) : dx i (f*g)=dx i f*g+f*dx i g := d_mul i.succ f g
@[simp] theorem dx_sq (i : Fin 3) (f : Scalar) : dx i (f^2)=C 2*f*dx i f := d_sq i.succ f

def dot (u v : Vector) : Scalar := u 0*v 0+u 1*v 1+u 2*v 2
def normSq (u : Vector) : Scalar := dot u u
def scale (a : Scalar) (v : Vector) : Vector := fun i => a*v i

def cross (u v : Vector) : Vector :=
  ![u 1*v 2-u 2*v 1, u 2*v 0-u 0*v 2, u 0*v 1-u 1*v 0]

def grad (f : Scalar) : Vector := fun i => dx i f
def div (v : Vector) : Scalar := dx 0 (v 0)+dx 1 (v 1)+dx 2 (v 2)
def curl (v : Vector) : Vector :=
  ![dx 1 (v 2)-dx 2 (v 1), dx 2 (v 0)-dx 0 (v 2), dx 0 (v 1)-dx 1 (v 0)]
def dtV (v : Vector) : Vector := fun i => dt (v i)
def adv (v : Vector) (f : Scalar) : Scalar := dot v (grad f)
def material (v : Vector) (f : Scalar) : Scalar := dt f+adv v f
def conservative (v : Vector) (f : Scalar) : Scalar := dt f+div (scale f v)
def materialV (v u : Vector) : Vector := fun i => material v (u i)
def advV (v u : Vector) : Vector := fun i => adv v (u i)

def matvec (M : Tensor) (v : Vector) : Vector := fun i =>
  M i 0*v 0+M i 1*v 1+M i 2*v 2

def transpose (M : Tensor) : Tensor := fun i j => M j i

def divTensor (M : Tensor) : Vector := fun i =>
  dx 0 (M i 0)+dx 1 (M i 1)+dx 2 (M i 2)

def stressWork (M : Tensor) (v : Vector) : Scalar :=
  M 0 0*dx 0 (v 0)+M 0 1*dx 1 (v 0)+M 0 2*dx 2 (v 0)+
  M 1 0*dx 0 (v 1)+M 1 1*dx 1 (v 1)+M 1 2*dx 2 (v 1)+
  M 2 0*dx 0 (v 2)+M 2 1*dx 1 (v 2)+M 2 2*dx 2 (v 2)

def massResidual (rho : Scalar) (v : Vector) : Scalar := conservative v rho

def conservativeMomentum (rho : Scalar) (v : Vector) : Vector := fun i =>
  dt (rho*v i)+div (scale (rho*v i) v)

/-- Standard reduced Eulerian variation, with arbitrary displacement. -/
def velocityVariation (v xi : Vector) : Vector := dtV xi+advV v xi-advV xi v
def densityVariation (rho : Scalar) (xi : Vector) : Scalar := -div (scale rho xi)
def scalarVariation (T : Scalar) (xi : Vector) : Scalar := -adv xi T

/-- Spacetime divergence and the current formed by a time density and spatial flux. -/
def div4 (F : Vector4) : Scalar := d 0 (F 0)+d 1 (F 1)+d 2 (F 2)+d 3 (F 3)
def spacetimeCurrent (u : Scalar) (F : Vector) : Vector4 := ![u,F 0,F 1,F 2]

@[simp] theorem div4_current (u : Scalar) (F : Vector) :
    div4 (spacetimeCurrent u F) = dt u+div F := by
  simp [div4, spacetimeCurrent, dt, div, dx, add_assoc]

/-- All spatial operators use the Euclidean Cartesian derivative. -/
theorem div_curl (A : Vector) : div (curl A) = 0 := by
  simp [div, curl, dx, d_comm]

theorem curl_grad (f : Scalar) : curl (grad f) = 0 := by
  funext i
  fin_cases i <;> simp [curl, grad, dx, d_comm]

theorem dt_curl (A : Vector) : dtV (curl A) = curl (dtV A) := by
  funext i
  fin_cases i <;> simp [dtV, curl, dt, dx, d_comm]

theorem curl_add (u v : Vector) : curl (u+v) = curl u+curl v := by
  funext i
  fin_cases i <;> simp [curl, dx, d_add] <;> ring

theorem curl_neg (v : Vector) : curl (-v) = -curl v := by
  funext i
  fin_cases i <;> simp [curl, dx, d_neg] <;> ring

theorem curl_sub (u v : Vector) : curl (u-v) = curl u-curl v := by
  simp only [sub_eq_add_neg, curl_add, curl_neg]

theorem curl_C_scale (c : ℝ) (v : Vector) : curl (scale (C c) v) = scale (C c) (curl v) := by
  funext i
  fin_cases i <;> simp [curl, scale, dx, d_mul] <;> ring

theorem dot_comm (u v : Vector) : dot u v = dot v u := by
  unfold dot
  ring

theorem dot_cross (u v w : Vector) : dot u (cross v w) = dot v (cross w u) := by
  simp [dot, cross]
  ring

theorem cross_antisymm (u v : Vector) : cross u v = -cross v u := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

@[simp] theorem cross_self (v : Vector) : cross v v=0 := by
  funext i
  fin_cases i <;> simp [cross, mul_comm]

theorem dot_scale_left (f : Scalar) (u v : Vector) : dot (scale f u) v=f*dot u v := by
  simp [dot,scale]
  ring

theorem dot_scale_right (f : Scalar) (u v : Vector) : dot u (scale f v)=f*dot u v := by
  simp [dot,scale]
  ring

theorem div_scale (f : Scalar) (v : Vector) :
    div (scale f v) = adv v f+f*div v := by
  simp [div, scale, adv, dot, grad, dx, d_mul]
  ring

theorem conservative_split (v : Vector) (f : Scalar) :
    conservative v f = material v f+f*div v := by
  simp [conservative, material, div_scale]
  ring

theorem material_mul (v : Vector) (f g : Scalar) :
    material v (f*g) = material v f*g+f*material v g := by
  simp [material, dt, adv, grad, dot, dx, d_mul]
  ring

theorem conservative_product (v : Vector) (rho f : Scalar) :
    conservative v (rho*f) = f*massResidual rho v+rho*material v f := by
  simp [conservative_split, material_mul, massResidual]
  ring

theorem conservative_momentum_split (rho : Scalar) (v : Vector) :
    conservativeMomentum rho v = scale rho (materialV v v)+scale (massResidual rho v) v := by
  funext i
  simpa [conservativeMomentum, conservative, scale, materialV, mul_comm, add_comm]
    using conservative_product v rho (v i)

/-- The constrained variations are tangent to the mass-continuity manifold.
    This identity is proved OFF SHELL: no mass equation is needed. -/
theorem linearized_mass_transport (rho : Scalar) (v xi : Vector) :
    dt (densityVariation rho xi)+
      div (scale (densityVariation rho xi) v+scale rho (velocityVariation v xi)) =
      -div (scale (massResidual rho v) xi) := by
  simp only [densityVariation, velocityVariation, massResidual, conservative,
    dtV, advV, adv, grad, scale, dot, div, dt, dx,
    Pi.add_apply, Pi.sub_apply, d_add, d_sub, d_neg, d_mul]
  simp only [d_comm]
  ring

/-- Magnetic energy integration by parts, BEFORE any field equation. -/
theorem magnetic_weak_identity (B a : Vector) :
    -dot B (curl a) = -dot (curl B) a-div (cross a B) := by
  simp [dot, curl, div, cross, dx, d_mul]
  ring

theorem stress_weak_identity (tau : Tensor) (xi : Vector) :
    -stressWork tau xi = dot (divTensor tau) xi-div (matvec (transpose tau) xi) := by
  simp [stressWork, dot, divTensor, div, matvec, transpose, dx, d_mul]
  ring

theorem poynting_product_rule (E B : Vector) :
    div (cross E B) = dot B (curl E)-dot E (curl B) := by
  simp [div, cross, dot, curl, dx, d_mul]
  ring

theorem material_divergence_kinetic (rho : Scalar) (v : Vector) :
    dt (C (1/2)*rho*normSq v)+div (scale (C (1/2)*rho*normSq v) v) =
      dot v (conservativeMomentum rho v)-C (1/2)*normSq v*massResidual rho v := by
  simp [dt, div, scale, normSq, dot, conservativeMomentum, massResidual,
    conservative, dx, d_mul]
  ext p
  simp only [eval_add,eval_sub,eval_mul,eval_neg,eval_zero,eval_one,eval_C,eval_pow]
  ring

/-- Evaluation helpers for constitutive passivity. -/
def valueV (v : Vector) (p : ST) : Fin 3 → ℝ := fun i => v i p
def rdot (u v : Fin 3 → ℝ) : ℝ := u 0*v 0+u 1*v 1+u 2*v 2
@[simp] theorem dot_eval (u v : Vector) (p : ST) :
    dot u v p = rdot (valueV u p) (valueV v p) := rfl

theorem normSq_nonnegative (u : Vector) (p : ST) : 0 ≤ normSq u p := by
  change 0 ≤ u 0 p*u 0 p+u 1 p*u 1 p+u 2 p*u 2 p
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    (mul_self_nonneg _)

end PdelEulerian
