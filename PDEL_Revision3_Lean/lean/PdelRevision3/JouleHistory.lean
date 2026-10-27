import PdelRevision3.CumulativeBudget

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace PdelRevision3

def historyCoordinate (a : ℝ) : ℝ := a ^ (-3/2 : ℝ)
def referenceJouleProfile (C a : ℝ) : ℝ := C * (1-historyCoordinate a)
def currentJouleProfile (C a : ℝ) : ℝ :=
  C * (historyCoordinate a)^2 * (1-historyCoordinate a)
def peakScale : ℝ := (3/2 : ℝ) ^ (2/3 : ℝ)
def peakTime (U : ℝ) : ℝ := (peakScale-1)/U

theorem current_profile_density (C a : ℝ) (ha : 0 < a) :
    currentJouleProfile C a = a ^ (-3 : ℝ) * referenceJouleProfile C a := by
  have hp : (historyCoordinate a)^2 = a ^ (-3 : ℝ) := by
    unfold historyCoordinate
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  rw [currentJouleProfile, hp, referenceJouleProfile]
  ring

theorem peakScale_gt_one : 1 < peakScale :=
  Real.one_lt_rpow (by norm_num) (by norm_num)

theorem historyCoordinate_peak : historyCoordinate peakScale = 2/3 := by
  unfold historyCoordinate peakScale
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3/2)]
  norm_num [Real.rpow_neg_one]

theorem historyCoordinate_hasDerivAt (a : ℝ) (ha : 0 < a) :
    HasDerivAt historyCoordinate ((-3/2 : ℝ)*a^(-5/2 : ℝ)) a := by
  convert Real.hasDerivAt_rpow_const (x:=a) (p:=(-3/2 : ℝ)) (Or.inl (ne_of_gt ha)) using 1 <;>
    norm_num [historyCoordinate]

theorem reference_profile_hasDerivAt (C a : ℝ) (ha : 0 < a) :
    HasDerivAt (referenceJouleProfile C) ((3*C/2)*a^(-5/2 : ℝ)) a := by
  convert (((hasDerivAt_const a (1:ℝ)).sub (historyCoordinate_hasDerivAt a ha)).const_mul C) using 1 <;> ring

/-- Material-scale derivative of the current-volume density, including dilution. -/
theorem current_profile_hasDerivAt (C a : ℝ) (ha : 0 < a) :
    HasDerivAt (currentJouleProfile C)
      ((3*C/2)*a^(-5/2 : ℝ)*historyCoordinate a*(3*historyCoordinate a-2)) a := by
  have hx := historyCoordinate_hasDerivAt a ha
  convert ((hx.pow 2).mul ((hasDerivAt_const a (1:ℝ)).sub hx)).const_mul C using 1
  · funext x
    unfold currentJouleProfile
    ring
  · ring

theorem current_profile_peak_value (C : ℝ) : currentJouleProfile C peakScale = 4*C/27 := by
  rw [currentJouleProfile, historyCoordinate_peak]
  ring

theorem current_profile_global_max (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a) :
    currentJouleProfile C a ≤ currentJouleProfile C peakScale := by
  have hx : 0 ≤ historyCoordinate a := (Real.rpow_pos_of_pos ha _).le
  have hg : 0 ≤ (historyCoordinate a-2/3)^2*(historyCoordinate a+1/3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hb : (historyCoordinate a)^2*(1-historyCoordinate a) ≤ (4/27 : ℝ) := by nlinarith
  rw [current_profile_peak_value, currentJouleProfile]
  nlinarith [mul_le_mul_of_nonneg_left hb hC]

theorem current_profile_derivative_positive (C a : ℝ) (hC : 0 < C)
    (ha : 0 < a) (hpeak : a < peakScale) : 0 < deriv (currentJouleProfile C) a := by
  have hx : (2/3 : ℝ) < historyCoordinate a := by
    rw [← historyCoordinate_peak]
    exact Real.rpow_lt_rpow_of_exponent_neg ha hpeak (by norm_num)
  rw [(current_profile_hasDerivAt C a ha).deriv]
  exact mul_pos (mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos ha _))
    (Real.rpow_pos_of_pos ha _)) (by linarith)

theorem current_profile_derivative_negative (C a : ℝ) (hC : 0 < C)
    (hpeak : peakScale < a) : deriv (currentJouleProfile C) a < 0 := by
  have hp : 0 < peakScale := lt_trans zero_lt_one peakScale_gt_one
  have ha := hp.trans hpeak
  have hx : historyCoordinate a < (2/3 : ℝ) := by
    rw [← historyCoordinate_peak]
    exact Real.rpow_lt_rpow_of_exponent_neg hp hpeak (by norm_num)
  rw [(current_profile_hasDerivAt C a ha).deriv]
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (by positivity)
    (Real.rpow_pos_of_pos ha _)) (Real.rpow_pos_of_pos ha _)) (by linarith)

theorem current_profile_derivative_at_peak (C : ℝ) :
    deriv (currentJouleProfile C) peakScale = 0 := by
  rw [(current_profile_hasDerivAt C peakScale (lt_trans zero_lt_one peakScale_gt_one)).deriv,
    historyCoordinate_peak]
  ring

theorem current_profile_increasing (C : ℝ) (hC : 0 < C) :
    StrictMonoOn (currentJouleProfile C) (Ioc 0 peakScale) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 peakScale)
  · intro a ha
    exact (current_profile_hasDerivAt C a ha.1).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Ioc] at ha
    exact current_profile_derivative_positive C a hC ha.1 ha.2

theorem current_profile_decreasing (C : ℝ) (hC : 0 < C) :
    StrictAntiOn (currentJouleProfile C) (Ici peakScale) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici peakScale)
  · intro a ha
    exact (current_profile_hasDerivAt C a
      (lt_of_lt_of_le (lt_trans zero_lt_one peakScale_gt_one) ha)).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Ici] at ha
    exact current_profile_derivative_negative C a hC ha

/-- Here C = b_*^2 g / 6 and U = 4 kappa_0. The integrand is the
reference-volume Joule power after multiplying eq:powers by a^3. -/
def referenceJouleHistory (C U t : ℝ) : ℝ :=
  ∫ s in (0)..t, (3*C*U/2)*(expansionScale U s)^(-5/2 : ℝ)

def currentJouleHistory (C U t : ℝ) : ℝ :=
  (expansionScale U t)^(-3 : ℝ)*referenceJouleHistory C U t

theorem scale_hasDerivAt (U t : ℝ) : HasDerivAt (expansionScale U) U t := by
  convert ((hasDerivAt_id t).const_mul U).const_add 1 using 1 <;> simp [expansionScale]

theorem scale_positive_between (U t : ℝ) (hU : 0 ≤ U)
    (ha : 0 < expansionScale U t) {s : ℝ} (hs : s ∈ uIcc 0 t) :
    0 < expansionScale U s := by
  rcases le_total 0 t with ht | ht
  · exact expansionScale_positive hU (uIcc_of_le ht ▸ hs).1
  · have hst : t ≤ s := (uIcc_of_ge ht ▸ hs).1
    have hm := mul_le_mul_of_nonneg_left hst hU
    unfold expansionScale at *
    linarith

theorem reference_history_closed (C U t : ℝ) (hU : 0 ≤ U)
    (ha : 0 < expansionScale U t) :
    referenceJouleHistory C U t = referenceJouleProfile C (expansionScale U t) := by
  have hd : ∀ s ∈ uIcc 0 t, HasDerivAt
      (fun s => referenceJouleProfile C (expansionScale U s))
      ((3*C*U/2)*(expansionScale U s)^(-5/2 : ℝ)) s := by
    intro s hs
    convert (reference_profile_hasDerivAt C _ (scale_positive_between U t hU ha hs)).comp s
      (scale_hasDerivAt U s) using 1 <;> ring
  have hi : IntervalIntegrable (fun s => (3*C*U/2)*(expansionScale U s)^(-5/2 : ℝ)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    exact (continuousAt_const.mul ((scale_hasDerivAt U s).continuousAt.rpow_const
      (Or.inl (ne_of_gt (scale_positive_between U t hU ha hs))))).continuousWithinAt
  rw [referenceJouleHistory, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [referenceJouleProfile, historyCoordinate, expansionScale]

theorem current_history_closed (C U t : ℝ) (hU : 0 ≤ U)
    (ha : 0 < expansionScale U t) :
    currentJouleHistory C U t = currentJouleProfile C (expansionScale U t) := by
  rw [currentJouleHistory, reference_history_closed C U t hU ha,
    current_profile_density C _ ha]

theorem current_history_hasDerivAt (C U t : ℝ) (hU : 0 ≤ U)
    (ha : 0 < expansionScale U t) :
    HasDerivAt (currentJouleHistory C U)
      (((3*C/2)*(expansionScale U t)^(-5/2 : ℝ)*historyCoordinate (expansionScale U t)*
        (3*historyCoordinate (expansionScale U t)-2))*U) t := by
  have he : ∀ᶠ s in 𝓝 t, 0 < expansionScale U s :=
    (isOpen_lt continuous_const (by unfold expansionScale; fun_prop)).mem_nhds ha
  have heq : currentJouleHistory C U =ᶠ[𝓝 t]
      (fun s => currentJouleProfile C (expansionScale U s)) := by
    filter_upwards [he] with s hs
    exact current_history_closed C U s hU hs
  exact ((current_profile_hasDerivAt C _ ha).comp t (scale_hasDerivAt U t)).congr_of_eventuallyEq heq

theorem scale_at_peakTime (U : ℝ) (hU : 0 < U) : expansionScale U (peakTime U) = peakScale := by
  unfold expansionScale peakTime
  field_simp [ne_of_gt hU] <;> ring

theorem current_history_peak (C U : ℝ) (hU : 0 < U) :
    currentJouleHistory C U (peakTime U) = 4*C/27 := by
  rw [current_history_closed C U _ hU.le (by rw [scale_at_peakTime U hU]; exact lt_trans zero_lt_one peakScale_gt_one),
    scale_at_peakTime U hU, current_profile_peak_value]

theorem current_history_global_max (C U t : ℝ) (hC : 0 ≤ C) (hU : 0 < U) (ht : 0 ≤ t) :
    currentJouleHistory C U t ≤ currentJouleHistory C U (peakTime U) := by
  rw [current_history_closed C U t hU.le (expansionScale_positive hU.le ht), current_history_peak C U hU,
    ← current_profile_peak_value]
  exact current_profile_global_max C _ hC (expansionScale_positive hU.le ht)

theorem peakTime_positive (U : ℝ) (hU : 0 < U) : 0 < peakTime U :=
  div_pos (sub_pos.mpr peakScale_gt_one) hU

theorem scale_le_peak_iff (U t : ℝ) (hU : 0 < U) :
    expansionScale U t ≤ peakScale ↔ t ≤ peakTime U := by
  rw [← scale_at_peakTime U hU]
  simp only [expansionScale, add_le_add_iff_left, mul_le_mul_left hU]

theorem current_history_increasing (C U : ℝ) (hC : 0 < C) (hU : 0 < U) :
    StrictMonoOn (currentJouleHistory C U) (Icc 0 (peakTime U)) := by
  intro s hs t ht hst
  rw [current_history_closed C U s hU.le (expansionScale_positive hU.le hs.1),
    current_history_closed C U t hU.le (expansionScale_positive hU.le ht.1)]
  apply current_profile_increasing C hC
  · exact ⟨expansionScale_positive hU.le hs.1, (scale_le_peak_iff U s hU).mpr hs.2⟩
  · exact ⟨expansionScale_positive hU.le ht.1, (scale_le_peak_iff U t hU).mpr ht.2⟩
  · exact add_lt_add_left (mul_lt_mul_of_pos_left hst hU) 1

theorem current_history_decreasing (C U : ℝ) (hC : 0 < C) (hU : 0 < U) :
    StrictAntiOn (currentJouleHistory C U) (Ici (peakTime U)) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := (peakTime_positive U hU).le.trans hs
  have ht0 : 0 ≤ t := (peakTime_positive U hU).le.trans ht
  rw [current_history_closed C U s hU.le (expansionScale_positive hU.le hs0),
    current_history_closed C U t hU.le (expansionScale_positive hU.le ht0)]
  apply current_profile_decreasing C hC
  · rw [← scale_at_peakTime U hU]
    exact add_le_add_left (mul_le_mul_of_nonneg_left hs hU.le) 1
  · rw [← scale_at_peakTime U hU]
    exact add_le_add_left (mul_le_mul_of_nonneg_left ht hU.le) 1
  · exact add_lt_add_left (mul_lt_mul_of_pos_left hst hU) 1

theorem current_history_derivative_at_peak (C U : ℝ) (hU : 0 < U) :
    deriv (currentJouleHistory C U) (peakTime U) = 0 := by
  rw [(current_history_hasDerivAt C U _ hU.le
    (by rw [scale_at_peakTime U hU]; exact lt_trans zero_lt_one peakScale_gt_one)).deriv,
    scale_at_peakTime U hU, historyCoordinate_peak]
  ring

theorem reference_history_increasing (C U : ℝ) (hC : 0 < C) (hU : 0 < U) :
    StrictMonoOn (referenceJouleHistory C U) (Ici 0) := by
  intro s hs t ht hst
  have hspos := expansionScale_positive hU.le hs
  have htpos := expansionScale_positive hU.le ht
  rw [reference_history_closed C U s hU.le hspos, reference_history_closed C U t hU.le htpos]
  apply mul_lt_mul_of_pos_left _ hC
  apply sub_lt_sub_left
  exact Real.rpow_lt_rpow_of_exponent_neg hspos
    (add_lt_add_left (mul_lt_mul_of_pos_left hst hU) 1) (by norm_num)

/-- The scalar integral really uses the paper's a^3 D_J, not an assigned
closed formula. This does not certify the underlying toroidal embedding. -/
theorem paper_reference_joule_rate (kappa b g t : ℝ)
    (ha : 0 < expansionScale (4*kappa) t) :
    (expansionScale (4*kappa) t)^3 * branchJoulePower kappa b g t =
      (3*(b^2*g/6)*(4*kappa)/2)*(expansionScale (4*kappa) t)^(-5/2 : ℝ) := by
  have hp : (expansionScale (4*kappa) t)^3 *
      (expansionScale (4*kappa) t)^(-11/2 : ℝ) =
      (expansionScale (4*kappa) t)^(-5/2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha]
    norm_num
  unfold branchJoulePower
  calc
    _ = (kappa*b^2*g)*((expansionScale (4*kappa) t)^3 *
        (expansionScale (4*kappa) t)^(-11/2 : ℝ)) := by ring
    _ = _ := by rw [hp]; ring

theorem current_history_is_paper_integral (kappa b g t : ℝ) (hk : 0 ≤ kappa)
    (ha : 0 < expansionScale (4*kappa) t) :
    currentJouleHistory (b^2*g/6) (4*kappa) t =
      (expansionScale (4*kappa) t)^(-3 : ℝ) *
        ∫ s in (0)..t, (expansionScale (4*kappa) s)^3 * branchJoulePower kappa b g s := by
  unfold currentJouleHistory referenceJouleHistory
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact (paper_reference_joule_rate kappa b g s
    (scale_positive_between (4*kappa) t (by positivity) ha hs)).symm

theorem paper_current_history_peak (kappa b g : ℝ) (hk : 0 < kappa) :
    currentJouleHistory (b^2*g/6) (4*kappa) (peakTime (4*kappa)) = 2*b^2*g/81 := by
  rw [current_history_peak _ _ (by positivity)]
  ring

end PdelRevision3
