import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedFarNegativeSummability

/-!
# Quantitative distance gap on the far-negative ray

The floor inequality controls the angular frequency at the canonical lower
endpoint.  Moving a mode down by integer distance `d` adds exactly `2πd`, so
the phase-adapted left gap dominates that full angular increment.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.modeRangeLower_floor_baseline
    (t : ℝ) (a : ℤ)
    (ha : 1 ≤ a) :
    ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a ≤
      2 * Real.pi *
        (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) := by
  let q :=
    (-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
      (2 * Real.pi)
  have hfloor :
      (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ) ≤ q := by
    unfold Complex.logarithmicPhasePoissonModeRangeLower
    exact Int.floor_le q
  have htwoPiPos := Complex.two_mul_pi_pos
  have hmul := mul_le_mul_of_nonneg_right hfloor htwoPiPos.le
  have hq : q * (2 * Real.pi) =
      -‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a := by
    unfold q
    exact div_mul_cancel₀ _ (ne_of_gt htwoPiPos)
  have hleftProduct :
      (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ) *
          (2 * Real.pi) =
        2 * Real.pi *
          (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ) :=
    mul_comm _ _
  have hnormalized :
      2 * Real.pi *
          (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ) ≤
        -‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a :=
    Eq.subst hleftProduct.symm (Eq.subst hq.symm hmul)
  have hneg := neg_le_neg hnormalized
  have hleftNeg :
      -(2 * Real.pi *
        (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) =
      2 * Real.pi *
        (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) :=
    (mul_neg (2 * Real.pi)
      (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)).symm
  have hrightNeg :
      -(-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) =
        ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a := by
    exact Eq.trans
      (neg_div (-‖t‖) (Real.integerBlockCutoffSupportLeftEndpoint a))
      (congrArg (fun value : ℝ => value /
        Real.integerBlockCutoffSupportLeftEndpoint a) (neg_neg ‖t‖))
  exact Eq.subst hrightNeg.symm (Eq.subst hleftNeg.symm hneg)

theorem Complex.modeRangeLower_quantitative_baseline
    (t : ℝ) (a : ℤ)
    (ha : 1 ≤ a) :
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a ≤
      2 * Real.pi *
        (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) := by
  exact le_trans
    (Complex.div_wideSupport_ge_div_quantitativeSupport t a ha)
    (Complex.modeRangeLower_floor_baseline t a ha)

theorem Complex.farNegative_angular_decomposition
    (t : ℝ) (a m : ℤ) :
    2 * Real.pi * (-(m : ℝ)) =
      2 * Real.pi *
        (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) +
      2 * Real.pi *
        (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) := by
  unfold Complex.logarithmicPhaseFarNegativeDistance
  have hcast :
      ((Complex.logarithmicPhasePoissonModeRangeLower t a - m : ℤ) : ℝ) =
        (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ) - (m : ℝ) :=
    Int.cast_sub _ _
  have hinside :
      -(m : ℝ) =
        -(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ) +
          ((Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ) -
            (m : ℝ)) := by
    exact Eq.trans
      (Eq.symm (zero_add (-(m : ℝ))))
      (congrArg (fun value : ℝ => value + -(m : ℝ))
        (Eq.symm (add_neg_cancel
          (Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)))).symm
  exact Eq.trans (congrArg (fun value : ℝ => 2 * Real.pi * value) hinside)
    (Eq.trans (mul_add _ _ _)
      (congrArg (fun value : ℝ =>
        2 * Real.pi *
          (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) +
        2 * Real.pi * value) hcast.symm))

theorem Complex.farNegative_distance_gap_le
    (t : ℝ) (a : ℤ)
    (ha : 1 ≤ a)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    2 * Real.pi *
        (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) ≤
      Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  unfold Complex.logarithmicPhaseLeftInactiveGap
  have hbaseline := Complex.modeRangeLower_quantitative_baseline t a ha
  have hdecompose := Complex.farNegative_angular_decomposition t a m
  have hsubtract := sub_le_sub_right hbaseline
    (2 * Real.pi * (-(m : ℝ)))
  have hnormalize :
      2 * Real.pi * (-(m : ℝ)) -
          2 * Real.pi *
            (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)) =
        2 * Real.pi *
          (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value -
        2 * Real.pi *
          (-(Complex.logarithmicPhasePoissonModeRangeLower t a : ℝ)))
        hdecompose)
      (add_sub_cancel_left _ _)
  have horiented := sub_le_sub_left hbaseline
    (2 * Real.pi * (-(m : ℝ)))
  exact Eq.subst hnormalize.symm horiented

end
end LFunctions
end Boundary
