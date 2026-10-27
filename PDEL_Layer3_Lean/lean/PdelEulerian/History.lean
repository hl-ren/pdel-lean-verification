import PdelEulerian.Fields

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace PdelEulerian

abbrev Label := Fin 3 → ℝ

def tangent (v : Vector) (p : ST) : ST := ![1,v 0 p,v 1 p,v 2 p]

/-- Evaluation of a real Frechet derivative on the actual spacetime velocity. -/
theorem fderiv_tangent (f : Scalar) (v : Vector) (p : ST) :
    fderiv ℝ (f : ST → ℝ) p (tangent v p) = material v f p := by
  have hv : tangent v p =
      (Pi.single 0 1 : ST)+v 0 p • (Pi.single 1 1 : ST)+
        v 1 p • (Pi.single 2 1 : ST)+v 2 p • (Pi.single 3 1 : ST) := by
    funext i
    fin_cases i <;> simp [tangent, Pi.single_apply]
  rw [hv]
  simp [material, dt, adv, dot, grad, dx, d, mul_comm, add_assoc]

/-- Actual affine endpoint chain rule, with the base-point conversion explicit. -/
theorem shifted_endpoint_hasDerivAt {f : ℝ → ℝ} {f' t : ℝ}
    (hf : HasDerivAt f f' t) (selector : ℝ) :
    HasDerivAt (fun e : ℝ => f (t+e*selector)) (f'*selector) 0 := by
  have hu : HasDerivAt (fun e : ℝ => t+e*selector) selector 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const selector).const_add t
  have hf0 : HasDerivAt f f' (t+(0 : ℝ)*selector) := by simpa using hf
  simpa using hf0.comp 0 hu

/-- Kinematic characteristic chart and volume factor. These fields contain only
    flow, label, and Liouville relations. There is NO MHD field equation here.
    The determinant-to-Liouville calculation is separately supplied below. -/
structure MaterialChart (v : Vector) where
  position : ℝ → Label → ST
  label : ST → Label
  volumeFactor : ℝ → Label → ℝ
  position_time : ∀ t X, position t X 0=t
  position_label : ∀ p, position (p 0) (label p)=p
  label_position : ∀ t X, label (position t X)=X
  position_deriv : ∀ t X,
    HasDerivAt (fun u => position u X) (tangent v (position t X)) t
  volume_pos : ∀ t X, 0 < volumeFactor t X
  volume_deriv : ∀ t X,
    HasDerivAt (fun u => volumeFactor u X)
      (volumeFactor t X*div v (position t X)) t

namespace MaterialChart

variable {v : Vector} (F : MaterialChart v)

theorem position_continuous (X : Label) : Continuous (fun t => F.position t X) :=
  continuous_iff_continuousAt.mpr (fun t => (F.position_deriv t X).continuousAt)

theorem volume_continuous (X : Label) : Continuous (fun t => F.volumeFactor t X) :=
  continuous_iff_continuousAt.mpr (fun t => (F.volume_deriv t X).continuousAt)

/-- Chain rule along the supplied material motion, using the correct base point. -/
theorem along_flow_hasDerivAt (f : Scalar) (t : ℝ) (X : Label) :
    HasDerivAt (fun u => f (F.position u X))
      (material v f (F.position t X)) t := by
  have h := (f.hasFDerivAt (F.position t X)).comp_hasDerivAt t (F.position_deriv t X)
  simpa only [fderiv_tangent] using h

def refHistory (D : Scalar) (t0 t : ℝ) (X : Label) : ℝ :=
  ∫ u in t0..t, F.volumeFactor u X*D (F.position u X)

def currentHistory (D : Scalar) (t0 : ℝ) (p : ST) : ℝ :=
  F.refHistory D t0 (p 0) (F.label p)/F.volumeFactor (p 0) (F.label p)

/-- The receiver operation changes the reference upper limit only. The current
    evaluation volume is held fixed in this endpoint operation. -/
def receiverHistory (D : Scalar) (t0 : ℝ) (p : ST) (upper : ℝ) : ℝ :=
  F.refHistory D t0 upper (F.label p)/F.volumeFactor (p 0) (F.label p)

theorem refHistory_hasDerivAt (D : Scalar) (t0 t : ℝ) (X : Label) :
    HasDerivAt (fun u => F.refHistory D t0 u X)
      (F.volumeFactor t X*D (F.position t X)) t := by
  have hc : Continuous (fun u => F.volumeFactor u X*D (F.position u X)) :=
    (F.volume_continuous X).mul (D.continuous.comp (F.position_continuous X))
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable t0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem receiver_endpoint_derivative (D : Scalar) (t0 : ℝ) (p : ST) (selector : ℝ) :
    HasDerivAt (fun e => F.receiverHistory D t0 p (p 0+e*selector))
      (D p*selector) 0 := by
  have hh := (F.refHistory_hasDerivAt D t0 (p 0) (F.label p)).div_const
    (F.volumeFactor (p 0) (F.label p))
  have hc := shifted_endpoint_hasDerivAt hh selector
  simpa [receiverHistory, F.position_label p,
    ne_of_gt (F.volume_pos (p 0) (F.label p))] using hc

theorem receiver_at_current (D : Scalar) (t0 : ℝ) (p : ST) :
    F.receiverHistory D t0 p (p 0)=F.currentHistory D t0 p := rfl

/-- A current-volume STATE density uses the conservative rate in its channel.
The reference density is evaluated at the shifted material endpoint while the
current denominator is frozen. This proves why Cs, not Ds, multiplies delta t_s. -/
theorem density_channel_derivative (f : Scalar) (p : ST) (selector : ℝ) :
    HasDerivAt (fun e : ℝ =>
      F.volumeFactor (p 0+e*selector) (F.label p)*
        f (F.position (p 0+e*selector) (F.label p))/
        F.volumeFactor (p 0) (F.label p))
      (conservative v f p*selector) 0 := by
  have hf := F.along_flow_hasDerivAt f (p 0) (F.label p)
  have hprod := ((F.volume_deriv (p 0) (F.label p)).mul hf).div_const
    (F.volumeFactor (p 0) (F.label p))
  have h := shifted_endpoint_hasDerivAt hprod selector
  convert h using 1
  simp only [F.position_label p,fderiv_tangent,conservative_split,eval_add,eval_mul]
  field_simp [ne_of_gt (F.volume_pos (p 0) (F.label p))]
  ring

/-- Actual material derivative of the normalized committed history. -/
theorem material_history_derivative (D : Scalar) (t0 t : ℝ) (X : Label) :
    HasDerivAt (fun u => F.currentHistory D t0 (F.position u X))
      (D (F.position t X)-F.currentHistory D t0 (F.position t X)*
        div v (F.position t X)) t := by
  have h := (F.refHistory_hasDerivAt D t0 t X).div
    (F.volume_deriv t X) (ne_of_gt (F.volume_pos t X))
  convert h using 1
  · funext u
    simp [currentHistory, F.position_time, F.label_position]
  · simp only [currentHistory, F.position_time, F.label_position]
    field_simp [ne_of_gt (F.volume_pos t X)]
    ring

/-- If the pushed-forward history is a differentiable scalar field, its real
    Eulerian conservative derivative is its physical source. The differentiability
    assumption is analytic regularity, not the transport equation being concluded. -/
theorem eulerian_history_transport (D H : Scalar) (t0 : ℝ)
    (hH : ∀ p, H p=F.currentHistory D t0 p) :
    conservative v H=D := by
  ext p
  have hcomp := F.along_flow_hasDerivAt H (p 0) (F.label p)
  have hactual := F.material_history_derivative D t0 (p 0) (F.label p)
  have heq : (fun u => H (F.position u (F.label p))) =
      (fun u => F.currentHistory D t0 (F.position u (F.label p))) :=
    funext (fun u => hH _)
  rw [← heq] at hactual
  have hu := hcomp.unique hactual
  rw [conservative_split]
  simp only [eval_add, eval_mul]
  have hu' : material v H p=D p-H p*div v p := by
    simpa only [F.position_label p, ← hH p] using hu
  linarith

/-- Mass is imposed as the material-density constraint, not as an Euler--Lagrange
coefficient. Its spatial continuity equation is then a real chain-rule theorem. -/
theorem mass_conservation (rho : Scalar) (rhoRef : Label → ℝ)
    (hmass : ∀ t X, rho (F.position t X)*F.volumeFactor t X=rhoRef X) :
    massResidual rho v=0 := by
  ext p
  let X := F.label p
  have hr := F.along_flow_hasDerivAt rho (p 0) X
  have hj := F.volume_deriv (p 0) X
  have hc : (fun t => rho (F.position t X)*F.volumeFactor t X)=fun _ => rhoRef X :=
    funext (fun t => hmass t X)
  have hz : HasDerivAt (fun t => rho (F.position t X)*F.volumeFactor t X) 0 (p 0) := by
    rw [hc]
    exact hasDerivAt_const (p 0) (rhoRef X)
  have he := (hr.mul hj).unique hz
  have hjpos := F.volume_pos (p 0) X
  have hd : material v rho p+rho p*div v p=0 := by
    simp only [X, F.position_label p, fderiv_tangent] at he hjpos
    have hz : F.volumeFactor (p 0) (F.label p)*
        (material v rho p+rho p*div v p)=0 := by nlinarith [he]
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hjpos)
  simpa only [massResidual, conservative_split, eval_add, eval_mul, eval_zero] using hd

end MaterialChart

/-- Literal 3 by 3 determinant, used only for the kinematic Jacobi calculation. -/
def det3 (A : Fin 3 → Fin 3 → ℝ) : ℝ :=
  A 0 0*(A 1 1*A 2 2-A 1 2*A 2 1)-
  A 0 1*(A 1 0*A 2 2-A 1 2*A 2 0)+
  A 0 2*(A 1 0*A 2 1-A 1 1*A 2 0)

/-- The volume ODE used by MaterialChart follows from the genuine determinant
    derivative when the deformation gradient obeys Fdot=L F. -/
theorem determinant_liouville
    (F : ℝ → Fin 3 → Fin 3 → ℝ) (L : Fin 3 → Fin 3 → ℝ) (t : ℝ)
    (hF : ∀ i j, HasDerivAt (fun u => F u i j)
      (L i 0*F t 0 j+L i 1*F t 1 j+L i 2*F t 2 j) t) :
    HasDerivAt (fun u => det3 (F u)) ((L 0 0+L 1 1+L 2 2)*det3 (F t)) t := by
  have h := ((hF 0 0).mul (((hF 1 1).mul (hF 2 2)).sub ((hF 1 2).mul (hF 2 1)))).sub
    ((hF 0 1).mul (((hF 1 0).mul (hF 2 2)).sub ((hF 1 2).mul (hF 2 0))))
  have h' := h.add ((hF 0 2).mul
    (((hF 1 0).mul (hF 2 1)).sub ((hF 1 1).mul (hF 2 0))))
  convert h' using 1 <;> unfold det3 <;> ring

/-- Differentiating the material mass constraint gives the conservative density
    rate. No thermomechanical field equation is used. -/
theorem mass_from_material_constraint
    {rho jac : ℝ → ℝ} {dr j divv t rho0 : ℝ}
    (hr : HasDerivAt rho dr t) (hj : HasDerivAt jac (j*divv) t)
    (hjt : jac t=j) (hjpos : 0<j)
    (hmass : ∀ u, rho u*jac u=rho0) : dr+rho t*divv=0 := by
  have hc : (fun u => rho u*jac u)=(fun _ => rho0) := funext hmass
  have hz : HasDerivAt (fun u => rho u*jac u) 0 t := by
    rw [hc]
    exact hasDerivAt_const t rho0
  have he := (hr.mul hj).unique hz
  rw [hjt] at he
  have hzero : j*(dr+rho t*divv)=0 := by nlinarith [he]
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hjpos)

end PdelEulerian
