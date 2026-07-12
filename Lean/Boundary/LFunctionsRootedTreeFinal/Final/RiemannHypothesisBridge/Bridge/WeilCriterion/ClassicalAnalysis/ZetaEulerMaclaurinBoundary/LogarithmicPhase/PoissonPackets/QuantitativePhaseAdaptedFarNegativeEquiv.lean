import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedFarNegativeSplit

/-!
# Reindexing the far-negative ray by positive integers

Subtraction from the floor-defined lower endpoint gives an exact equivalence
between far-negative modes and positive integers.  This is the canonical
reindexing for the shifted inverse-square tail.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFarNegativeToPositive
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhasePoissonPositiveTailModes :=
  ⟨Complex.logarithmicPhaseFarNegativeDistance t a m,
    Complex.farNegativeDistance_pos t a m⟩

def Complex.logarithmicPhasePositiveToFarNegative
    (t : ℝ) (a : ℤ)
    (k : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhasePoissonFarNegativeModes t a :=
  ⟨Complex.logarithmicPhasePoissonModeRangeLower t a - (k : ℤ), by
    have hk : 0 < (k : ℤ) := k.property
    exact sub_lt_self _ hk⟩

theorem Complex.logarithmicPhaseFarNegativeToPositive_value
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    ((Complex.logarithmicPhaseFarNegativeToPositive t a m :
      Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) =
      Complex.logarithmicPhasePoissonModeRangeLower t a - (m : ℤ) := by
  exact rfl

theorem Complex.logarithmicPhasePositiveToFarNegative_value
    (t : ℝ) (a : ℤ)
    (k : Complex.logarithmicPhasePoissonPositiveTailModes) :
    ((Complex.logarithmicPhasePositiveToFarNegative t a k :
      Complex.logarithmicPhasePoissonFarNegativeModes t a) : ℤ) =
      Complex.logarithmicPhasePoissonModeRangeLower t a - (k : ℤ) := by
  exact rfl

theorem Complex.logarithmicPhaseFarNegativeToPositive_leftInverse
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhasePositiveToFarNegative t a
      (Complex.logarithmicPhaseFarNegativeToPositive t a m) = m := by
  exact Subtype.ext
    (Eq.trans
      (Complex.logarithmicPhasePositiveToFarNegative_value t a
        (Complex.logarithmicPhaseFarNegativeToPositive t a m))
      (Eq.trans
        (congrArg
          (fun value : ℤ =>
            Complex.logarithmicPhasePoissonModeRangeLower t a - value)
          (Complex.logarithmicPhaseFarNegativeToPositive_value t a m))
        (sub_sub_cancel_left
          (Complex.logarithmicPhasePoissonModeRangeLower t a) (m : ℤ))))

theorem Complex.logarithmicPhaseFarNegativeToPositive_rightInverse
    (t : ℝ) (a : ℤ)
    (k : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhaseFarNegativeToPositive t a
      (Complex.logarithmicPhasePositiveToFarNegative t a k) = k := by
  exact Subtype.ext
    (Eq.trans
      (Complex.logarithmicPhaseFarNegativeToPositive_value t a
        (Complex.logarithmicPhasePositiveToFarNegative t a k))
      (Eq.trans
        (congrArg
          (fun value : ℤ =>
            Complex.logarithmicPhasePoissonModeRangeLower t a - value)
          (Complex.logarithmicPhasePositiveToFarNegative_value t a k))
        (sub_sub_cancel_left
          (Complex.logarithmicPhasePoissonModeRangeLower t a) (k : ℤ))))

def Complex.logarithmicPhaseFarNegativeEquivPositive
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonFarNegativeModes t a ≃
      Complex.logarithmicPhasePoissonPositiveTailModes where
  toFun := Complex.logarithmicPhaseFarNegativeToPositive t a
  invFun := Complex.logarithmicPhasePositiveToFarNegative t a
  left_inv := Complex.logarithmicPhaseFarNegativeToPositive_leftInverse t a
  right_inv := Complex.logarithmicPhaseFarNegativeToPositive_rightInverse t a

theorem Complex.logarithmicPhaseFarNegativeEquivPositive_apply_coe
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    ((Complex.logarithmicPhaseFarNegativeEquivPositive t a m :
      Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) =
      Complex.logarithmicPhaseFarNegativeDistance t a m := by
  exact rfl

theorem Complex.logarithmicPhaseFarNegativeEquivPositive_symm_apply_coe
    (t : ℝ) (a : ℤ)
    (k : Complex.logarithmicPhasePoissonPositiveTailModes) :
    (((Complex.logarithmicPhaseFarNegativeEquivPositive t a).symm k :
      Complex.logarithmicPhasePoissonFarNegativeModes t a) : ℤ) =
      Complex.logarithmicPhasePoissonModeRangeLower t a - (k : ℤ) := by
  exact rfl

def Complex.logarithmicPhaseFarNegativeIntegerInverseSquare
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) : ℝ :=
  |(Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ)| ^ (-2 : ℝ)

theorem Complex.logarithmicPhaseFarNegativeIntegerInverseSquare_eq_positive
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhaseFarNegativeIntegerInverseSquare t a m =
      |(((Complex.logarithmicPhaseFarNegativeEquivPositive t a m :
        Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) : ℝ)| ^
        (-2 : ℝ) := by
  unfold Complex.logarithmicPhaseFarNegativeIntegerInverseSquare
  exact congrArg (fun value : ℝ => |value| ^ (-2 : ℝ))
    (congrArg (fun value : ℤ => (value : ℝ))
      (Complex.logarithmicPhaseFarNegativeEquivPositive_apply_coe t a m).symm)

end
end LFunctions
end Boundary
