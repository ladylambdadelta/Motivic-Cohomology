import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.FixedVerticalPoint
import Mathlib.Data.Real.Archimedean

/-!
# Deterministic vertical-strip shifts

This subowner contains the natural right shift used to move a real vertical
strip into the strict right half-plane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Deterministic right shift for a vertical strip.

It is a natural shift at least `1 - A`, so it moves the strip lower edge `A`
into the strict right half-plane with real part at least `1`. -/
def Complex.verticalStripRightShift (A : ℝ) : ℕ :=
  Nat.ceil (max 1 (1 - A))

/-- The deterministic strip shift dominates the negative lower endpoint. -/
theorem Complex.neg_lower_le_verticalStripRightShift
    (A : ℝ) :
    -A ≤ (Complex.verticalStripRightShift A : ℝ) :=
  let hneg_le_one_sub : -A ≤ 1 - A := by
    calc
      -A = 0 + -A := by
        exact (zero_add (-A)).symm
      _ ≤ 1 + -A :=
        add_le_add_right zero_le_one (-A)
      _ = 1 - A := (sub_eq_add_neg 1 A).symm
  let hmax : 1 - A ≤ max 1 (1 - A) :=
    le_max_right 1 (1 - A)
  let hceil : max 1 (1 - A) ≤ (Complex.verticalStripRightShift A : ℝ) :=
    Nat.le_ceil (max 1 (1 - A))
  le_trans hneg_le_one_sub (le_trans hmax hceil)

/-- The deterministic strip shift places the lower endpoint at real part at
least `1`. -/
theorem Complex.one_le_lower_add_verticalStripRightShift
    (A : ℝ) :
    1 ≤ A + (Complex.verticalStripRightShift A : ℝ) :=
  let hmax : 1 - A ≤ max 1 (1 - A) :=
    le_max_right 1 (1 - A)
  let hceil : max 1 (1 - A) ≤ (Complex.verticalStripRightShift A : ℝ) :=
    Nat.le_ceil (max 1 (1 - A))
  have hshift : 1 - A ≤ (Complex.verticalStripRightShift A : ℝ) :=
    le_trans hmax hceil
  calc
    1 = A + (1 - A) := by
      calc
        1 = (1 - A) + A := by
          exact (sub_add_cancel 1 A).symm
        _ = A + (1 - A) := by
          exact add_comm (1 - A) A
    _ ≤ A + (Complex.verticalStripRightShift A : ℝ) :=
      add_le_add_left hshift A

/-- The deterministic strip shift is nonnegative as a real number. -/
theorem Complex.verticalStripRightShift_nonneg
    (A : ℝ) :
    (0 : ℝ) ≤ (Complex.verticalStripRightShift A : ℝ) :=
  Nat.cast_nonneg (Complex.verticalStripRightShift A)

/-- Bounded intervals have a uniform absolute-value bound by the endpoint
absolute values. -/
theorem real_abs_le_max_abs_of_mem_Icc
    {A B x : ℝ}
    (hxA : A ≤ x)
    (hxB : x ≤ B) :
    |x| ≤ max |A| |B| := by
  have hmax_A : |A| ≤ max |A| |B| :=
    le_max_left |A| |B|
  have hmax_B : |B| ≤ max |A| |B| :=
    le_max_right |A| |B|
  have hleft_endpoint : -|A| ≤ A :=
    neg_abs_le A
  have hleft_max : -max |A| |B| ≤ -|A| :=
    neg_le_neg hmax_A
  have hleft : -max |A| |B| ≤ x :=
    le_trans hleft_max (le_trans hleft_endpoint hxA)
  have hright_endpoint : B ≤ |B| :=
    le_abs_self B
  have hright : x ≤ max |A| |B| :=
    le_trans hxB (le_trans hright_endpoint hmax_B)
  exact abs_le.mpr ⟨hleft, hright⟩

/-- The deterministic strip shift written as the transport shift used by
vertical recurrence. -/
def Complex.verticalStripTransportShift (A : ℝ) : ℕ :=
  Complex.verticalStripRightShift A

end
end LFunctions
end Boundary
