import PdelEulerian.Energy

/-!
# A nonempty, positive-dissipation continuum instance

This witness has genuine spatial curl, a time-dependent magnetic field, and
Joule heating. It is NOT a toroidal-confinement or stability result.
The scalar resistivity eta(t)=exp(t)/(1+exp(t)) is prescribed and smooth;
all spatial components of the Eulerian equations are still present.
-/

noncomputable section
open Set
namespace PdelEulerian
namespace Example

local instance : HasDistribNeg Scalar := inferInstance

theorem one_plus_exp_nonzero (p : ST) :
    (1+sexp (coordinate 0)) p≠0 := by
  have h := Real.exp_pos (p 0)
  simp only [eval_add,eval_one,sexp_apply,coordinate_apply]
  positivity

def amplitude : Scalar := reciprocal (1+sexp (coordinate 0)) one_plus_exp_nonzero

def diffusivity : Scalar := 1-amplitude

theorem amplitude_positive (p : ST) : 0 < amplitude p := by
  simp only [amplitude,reciprocal_apply,eval_add,eval_one,sexp_apply,coordinate_apply]
  positivity

theorem amplitude_lt_one (p : ST) : amplitude p<1 := by
  have he := Real.exp_pos (p 0)
  have hd : 0 < 1+Real.exp (p 0) := by linarith
  change (1+Real.exp (p 0))⁻¹<1
  rw [inv_eq_one_div,div_lt_iff₀ hd]
  linarith

theorem diffusivity_positive (p : ST) : 0 < diffusivity p := by
  change 0 < 1-amplitude p
  linarith [amplitude_lt_one p]

theorem diffusivity_nonzero (p : ST) : diffusivity p≠0 := ne_of_gt (diffusivity_positive p)

@[simp] theorem dt_amplitude : dt amplitude=-diffusivity*amplitude := by
  simp only [dt,amplitude,d_reciprocal,d_add,d_one,d_sexp,d_coordinate]
  ext p
  simp only [eval_add,eval_sub,eval_neg,eval_mul,eval_zero,eval_one,
    eval_C,eval_pow,reciprocal_apply,sexp_apply,coordinate_apply,diffusivity,amplitude]
  field_simp [one_plus_exp_nonzero p]
  ring

@[simp] theorem dx_amplitude (i : Fin 3) : dx i amplitude=0 := by
  fin_cases i <;>
    simp [dx,amplitude,d_reciprocal,d_add,d_sexp,d_coordinate]

def temp : Scalar := C 2-C (1/2)*amplitude^2

theorem temp_positive (p : ST) : 0<temp p := by
  have hb0 := amplitude_positive p
  have hb1 := amplitude_lt_one p
  change 0 < 2-(1/2 : ℝ)*(amplitude p)^2
  nlinarith

theorem temp_nonzero (p : ST) : temp p≠0 := ne_of_gt (temp_positive p)

def gas : Gas := ⟨1,1,1,1,by norm_num,by norm_num,by norm_num,by norm_num⟩

def thermalState : ThermalState where
  rho := 1
  temp := temp
  entropy := slog temp temp_nonzero
  rho_pos := by intro p; exact zero_lt_one
  temp_pos := temp_positive

def transport : Transport where
  eta := fun i j => if i=j then diffusivity else 0
  sigma := fun i j => if i=j then reciprocal diffusivity diffusivity_nonzero else 0
  inverse := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  eta_symmetric := by intro i j; simp [eq_comm]
  sigma_symmetric := by intro i j; simp [eq_comm]
  eta_pos := by
    classical
    intro p z hz
    have hsum : 0 < z 0*z 0+z 1*z 1+z 2*z 2 := by
      have h0 : 0 ≤ z 0*z 0+z 1*z 1+z 2*z 2 :=
        add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
      by_contra hh
      have he : z 0*z 0+z 1*z 1+z 2*z 2=0 := le_antisymm (le_of_not_gt hh) h0
      have hz0 : z 0=0 := by nlinarith [sq_nonneg (z 1),sq_nonneg (z 2)]
      have hz1 : z 1=0 := by nlinarith [sq_nonneg (z 0),sq_nonneg (z 2)]
      have hz2 : z 2=0 := by nlinarith [sq_nonneg (z 0),sq_nonneg (z 1)]
      apply hz
      funext i
      fin_cases i <;> simp [hz0,hz1,hz2]
    have hm := mul_pos (diffusivity_positive p) hsum
    simpa [rdot,mul_add,add_mul,mul_assoc,mul_left_comm,mul_comm] using hm
  sigma_nonneg := by
    intro p z
    have hi : 0 ≤ (diffusivity p)⁻¹ := (inv_pos.mpr (diffusivity_positive p)).le
    have hm := mul_nonneg hi
      (add_nonneg (add_nonneg (mul_self_nonneg (z 0)) (mul_self_nonneg (z 1))) (mul_self_nonneg (z 2)))
    simpa [rdot,mul_add,add_mul,mul_assoc,mul_left_comm,mul_comm] using hm
  bulk := 1
  thermal := 1
  bulk_nonneg := by intro; exact zero_le_one
  thermal_nonneg := by intro; exact zero_le_one

def fields : Fields where
  state := thermalState
  velocity := 0
  potential := ![-amplitude*scos (coordinate 3),-amplitude*ssin (coordinate 3),0]

@[simp] theorem dt_cosz : dt (scos (coordinate 3))=0 := by simp [dt]
@[simp] theorem dt_sinz : dt (ssin (coordinate 3))=0 := by simp [dt]
@[simp] theorem dx_cosz (i : Fin 3) :
    dx i (scos (coordinate 3))=if i=2 then -ssin (coordinate 3) else 0 := by
  fin_cases i <;> simp [dx]
@[simp] theorem dx_sinz (i : Fin 3) :
    dx i (ssin (coordinate 3))=if i=2 then scos (coordinate 3) else 0 := by
  fin_cases i <;> simp [dx]

@[simp] theorem dt_temp : dt temp=diffusivity*amplitude^2 := by
  simp only [temp,dt_sub,dt_C,dt_mul,dt_sq,dt_amplitude]
  apply scalar_ext
  intro p
  change 0 - (0 * (amplitude p)^2 + (1/2 : ℝ) *
    (2 * amplitude p * (-diffusivity p * amplitude p))) = diffusivity p * (amplitude p)^2
  ring

@[simp] theorem dx_temp (i : Fin 3) : dx i temp=0 := by
  simp [temp,dx_mul,dx_sq,dx_amplitude]

/-- Material chart at rest has exact unit Jacobian and is globally defined. -/
def chart : MaterialChart fields.velocity where
  position := fun t X => ![t,X 0,X 1,X 2]
  label := fun p => ![p 1,p 2,p 3]
  volumeFactor := fun _ _ => 1
  position_time := by intros; rfl
  position_label := by
    intro p
    funext i
    fin_cases i <;> rfl
  label_position := by
    intro t X
    funext i
    fin_cases i <;> rfl
  position_deriv := by
    intro t X
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [tangent,fields] using hasDerivAt_id t
    · simpa [tangent,fields] using hasDerivAt_const t (X 0)
    · simpa [tangent,fields] using hasDerivAt_const t (X 1)
    · simpa [tangent,fields] using hasDerivAt_const t (X 2)
  volume_pos := by intros; exact zero_lt_one
  volume_deriv := by
    intro t X
    simpa [fields,div,dx] using hasDerivAt_const t (1 : ℝ)

@[simp] theorem example_magnetic : fields.magnetic=
    ![amplitude*scos (coordinate 3),amplitude*ssin (coordinate 3),0] := by
  funext i
  fin_cases i <;>
    simp [Fields.magnetic,fields,curl,dx_mul,dx_neg,dx_amplitude,dx_cosz,dx_sinz]

@[simp] theorem example_current : fields.current = -fields.magnetic := by
  unfold Fields.current
  rw [example_magnetic]
  funext i
  fin_cases i <;> simp [curl,dx_mul,dx_amplitude,dx_cosz,dx_sinz]

theorem example_norm : normSq fields.magnetic=amplitude^2 := by
  rw [example_magnetic]
  have ht := ssin_sq_add_scos_sq (coordinate 3)
  simp only [normSq,dot,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ]
  linear_combination amplitude^2*ht

@[simp] theorem example_relative : fields.relativeRate=scale diffusivity fields.magnetic := by
  rw [example_magnetic]
  funext i
  fin_cases i <;>
    simp [Fields.relativeRate,fields,dtV,cross,scale,dt_mul,dt_neg,
      dt_amplitude,dt_cosz,dt_sinz] <;> ring

@[simp] theorem example_resistance : fields.resistance transport=fields.magnetic := by
  unfold Fields.resistance
  rw [example_relative]
  funext i
  fin_cases i <;>
    simp [transport,matvec,scale] <;>
    ext p <;>
    simp only [eval_mul,reciprocal_apply] <;>
    field_simp [diffusivity_nonzero p]

@[simp] theorem example_joule : fields.joulePower transport=diffusivity*amplitude^2 := by
  unfold Fields.joulePower
  rw [example_relative,example_resistance,dot_scale_left]
  change diffusivity*normSq fields.magnetic=diffusivity*amplitude^2
  rw [example_norm]

theorem example_joule_strictly_positive (p : ST) : 0<fields.joulePower transport p := by
  rw [example_joule]
  exact mul_pos (diffusivity_positive p) (sq_pos_of_pos (amplitude_positive p))

@[simp] theorem example_viscous : fields.viscousStress transport=0 := by
  funext i j
  simp [Fields.viscousStress,fields,div]

@[simp] theorem example_heatFlux : fields.heatFlux transport=0 := by
  funext i
  simp [Fields.heatFlux,fields,thermalState,grad,scale,dx_temp]

@[simp] theorem example_rho : fields.densityResidual=0 := by
  simp [Fields.densityResidual,fields,thermalState,massResidual,conservative,div,scale]

/-- Directly computed residual identities; these are not supplied as data in
Fields, Transport, or MaterialChart. -/
theorem example_primitive (Q : Box) : PrimitiveOn Q gas transport fields := by
  have hm : fields.momentumResidual gas transport=0 := by
    unfold Fields.momentumResidual
    rw [example_resistance,example_viscous,cross_self]
    funext i
    simp [fields,thermalState,gas,conservativeMomentum,divTensor,
      ThermalState.pressure_ideal_gas,grad,div,scale,dx_temp]
  have hA : fields.ohmResidual transport=0 := by
    unfold Fields.ohmResidual
    rw [example_current,example_resistance]
    simp
  have hT : fields.thermalResidual gas=0 := by
    ext p
    simp [Fields.thermalResidual,ThermalState.conjugacyResidual,
      ThermalState.phiTemp,ThermalState.logRho,ThermalState.logTemp,
      fields,thermalState,gas]
  have hS : fields.entropyResidual transport=0 := by
    rw [Fields.entropyResidual,example_heatFlux,example_joule,Fields.bulk_power]
    have ht : dt (slog temp temp_nonzero)=reciprocal temp temp_nonzero*(diffusivity*amplitude^2) := by
      change d 0 (slog temp temp_nonzero)=_
      rw [d_slog]
      change reciprocal temp temp_nonzero*dt temp=_
      rw [dt_temp]
    simp only [fields,thermalState,conservative,div,scale,Pi.zero_apply,
      mul_zero,dx_zero,add_zero,dt_zero,sub_zero,ht]
    ext p
    simp only [eval_mul,eval_sub,eval_zero,reciprocal_apply,eval_pow]
    field_simp [temp_nonzero p]
  intro p hp
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    exact congrArg (fun v : Vector => v i p) hm
  · intro i
    exact congrArg (fun v : Vector => v i p) hA
  · exact congrArg (fun f : Scalar => f p) hT
  · exact congrArg (fun f : Scalar => f p) hS

theorem example_stationary (Q : Box) (t0 : ℝ) :
    Stationary Q gas transport fields chart t0 :=
  (eulerian_pdel_variational_theorem Q gas transport fields chart t0).mpr
    (example_primitive Q)

theorem example_full_mhd (Q : Box) : EulerianMHDOn Q gas transport fields := by
  have hm : MassAdmissible Q fields := by
    intro p _
    exact congrArg (fun f : Scalar => f p) example_rho
  exact (eulerian_pdel_mhd_theorem Q gas transport fields chart 0 hm).mp
    (example_stationary Q 0)

end Example
end PdelEulerian
