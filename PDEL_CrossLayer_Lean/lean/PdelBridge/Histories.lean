import PdelBasic.History
import PdelBasic.Stationarity
import PdelEulerian.BoxIntegration

noncomputable section
namespace PdelBridge

/-- The Layer-3 reference history is exactly the Layer-2 time integral of
the pulled-back reference-volume power. -/
theorem reference_history_is_layer2 (v : PdelEulerian.Vector)
    (F : PdelEulerian.MaterialChart v) (D : PdelEulerian.Scalar)
    (a t : ℝ) (X : PdelEulerian.Label) :
    F.refHistory D a t X = PdelBasic.powerHistory
      (fun u => F.volumeFactor u X * D (F.position u X)) a t := rfl

theorem current_history_normalization (v : PdelEulerian.Vector)
    (F : PdelEulerian.MaterialChart v) (D : PdelEulerian.Scalar)
    (a : ℝ) (p : PdelEulerian.ST) :
    F.currentHistory D a p = PdelBasic.powerHistory
      (fun u => F.volumeFactor u (F.label p) * D (F.position u (F.label p))) a (p 0) /
        F.volumeFactor (p 0) (F.label p) := rfl

/-- The actual endpoint theorem of Layer 2 yields the receiver theorem of
Layer 3 after pullback, normalization, and the chart's current-point identity. -/
theorem receiver_derivative_via_layer2 (v : PdelEulerian.Vector)
    (F : PdelEulerian.MaterialChart v) (D : PdelEulerian.Scalar)
    (a : ℝ) (p : PdelEulerian.ST) (selector : ℝ) :
    HasDerivAt (fun e => F.receiverHistory D a p (p 0 + e * selector))
      (D p * selector) 0 := by
  have hc : Continuous (fun u => F.volumeFactor u (F.label p) * D (F.position u (F.label p))) :=
    (F.volume_continuous _).mul (D.continuous.comp (F.position_continuous _))
  have h := (PdelBasic.endpoint_channel_derivative hc a (p 0) selector).div_const
    (F.volumeFactor (p 0) (F.label p))
  convert h using 1
  simp only [F.position_label p]
  field_simp [ne_of_gt (F.volume_pos (p 0) (F.label p))]
  ring

theorem unit_volume_history (v : PdelEulerian.Vector)
    (F : PdelEulerian.MaterialChart v) (D : PdelEulerian.Scalar)
    (hunit : ∀ t X, F.volumeFactor t X = 1) (a : ℝ) (p : PdelEulerian.ST) :
    F.currentHistory D a p =
      PdelBasic.powerHistory (fun u => D (F.position u (F.label p))) a (p 0) := by
  simp [current_history_normalization, hunit]

/-- The four-dimensional localization weight is the product of the exact
one-dimensional endpoint weights used in Layer 2. -/
theorem box_weight_product (Q : PdelEulerian.Box) (p : PdelEulerian.ST) :
    Q.weight p =
      PdelBasic.endpointWeight (Q.lo 0) (Q.hi 0) (p 0) *
      PdelBasic.endpointWeight (Q.lo 1) (Q.hi 1) (p 1) *
      PdelBasic.endpointWeight (Q.lo 2) (Q.hi 2) (p 2) *
      PdelBasic.endpointWeight (Q.lo 3) (Q.hi 3) (p 3) := rfl

end PdelBridge
