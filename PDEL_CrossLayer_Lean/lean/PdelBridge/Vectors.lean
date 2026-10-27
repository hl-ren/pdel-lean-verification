import PdelMHD
import PdelEulerian.Fields

noncomputable section
namespace PdelBridge

abbrev RVector := Fin 3 → ℝ

def toV3 (v : RVector) : PdelMHD.V3 := ⟨v 0, v 1, v 2⟩
def fromV3 (v : PdelMHD.V3) : RVector := ![v.x, v.y, v.z]

@[simp] theorem to_from (v : PdelMHD.V3) : toV3 (fromV3 v) = v := by
  cases v
  rfl

@[simp] theorem from_to (v : RVector) : fromV3 (toV3 v) = v := by
  funext i
  fin_cases i <;> rfl

def vectorEquiv : RVector ≃ PdelMHD.V3 :=
  ⟨toV3, fromV3, from_to, to_from⟩

theorem toV3_zero_iff (v : RVector) : toV3 v = PdelMHD.zeroV ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg fromV3 h
    rw [from_to] at this
    have hz : fromV3 PdelMHD.zeroV = (0 : RVector) := by
      funext i
      fin_cases i <;> rfl
    exact this.trans hz
  · intro h
    subst v
    rfl

theorem dot_conversion (u v : RVector) :
    PdelMHD.dot (toV3 u) (toV3 v) = PdelEulerian.rdot u v := rfl

theorem dot_evaluation (u v : PdelEulerian.Vector) (p : PdelEulerian.ST) :
    PdelMHD.dot (toV3 (PdelEulerian.valueV u p)) (toV3 (PdelEulerian.valueV v p)) =
      PdelEulerian.dot u v p := rfl

theorem cross_evaluation (u v : PdelEulerian.Vector) (p : PdelEulerian.ST) :
    toV3 (PdelEulerian.valueV (PdelEulerian.cross u v) p) =
      PdelMHD.cross (toV3 (PdelEulerian.valueV u p)) (toV3 (PdelEulerian.valueV v p)) := by
  apply PdelMHD.V3.ext <;> rfl

theorem norm_evaluation (v : PdelEulerian.Vector) (p : PdelEulerian.ST) :
    PdelMHD.normSq (toV3 (PdelEulerian.valueV v p)) = PdelEulerian.normSq v p := rfl

/-- The Cartesian Lorentz power identity from Layer 1 holds for the actual
Layer-3 fields at every spacetime point; no field equation is assumed. -/
theorem lorentz_power_pointwise (J E v B : PdelEulerian.Vector) (p : PdelEulerian.ST) :
    PdelEulerian.dot J E p - PdelEulerian.dot v (PdelEulerian.cross J B) p =
      PdelEulerian.dot J E p + PdelEulerian.dot J (PdelEulerian.cross v B) p := by
  have h := PdelMHD.lorentz_power_split (toV3 (PdelEulerian.valueV J p))
    (toV3 (PdelEulerian.valueV E p)) (toV3 (PdelEulerian.valueV v p))
    (toV3 (PdelEulerian.valueV B p))
  simpa only [← cross_evaluation, dot_evaluation] using h

end PdelBridge
