import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedThreeComponent
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveGapCore

/-!
# Endpoint-enhanced positive-mode gap

For positive modes the derivative norm is `‖t‖/x + 2πm`.  On the support,
`x` is at most the right endpoint, so the full uniform gap retains the crucial
term `‖t‖/right`.  This term absorbs phase-curvature factors in the arithmetic
closure and must not be discarded.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.div_rightSupport_le_div_x
    (t : ℝ) {x right : ℝ}
    (hx : 0 < x) (hxright : x ≤ right) :
    ‖t‖ / right ≤ ‖t‖ / x := by
  exact Real.div_antitone_on_pos (norm_nonneg t) hx hxright

theorem Complex.logarithmicPhaseEnhancedPositiveModeDerivative_gap
    (t : ℝ) (a b m : ℤ) {x : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : 0 < m)
    (hx : x ∈ Set.uIcc
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) :
    Complex.logarithmicPhaseEnhancedPositiveModeGap t b m ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ := by
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hxIcc : x ∈ Set.Icc
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) :=
    Eq.subst
      (motive := fun interval : Set ℝ => x ∈ interval)
      (Set.uIcc_of_le hleftRight) hx
  have hxPos :=
    Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
  have hdivision := Complex.div_rightSupport_le_div_x t hxPos hxIcc.2
  have habs := Complex.abs_logarithmicPhasePositiveModeDerivative
    t x m hxPos (le_of_lt hm)
  unfold Complex.logarithmicPhaseEnhancedPositiveModeGap
  have hadd := add_le_add_right hdivision
    (Complex.logarithmicPhasePositiveModeGap m)
  exact le_trans hadd (le_of_eq habs.symm)

def Complex.logarithmicPhaseEnhancedPositiveModeClosedMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedClosedMajorant t a b
    (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)

theorem Complex.norm_logarithmicPhasePositiveModePacket_le_enhanced
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket (‖t‖) a b m‖ ≤
      Complex.logarithmicPhaseEnhancedPositiveModeClosedMajorant t a b m := by
  have hgap :=
    Complex.logarithmicPhaseEnhancedPositiveModeGap_pos t a b m ha hab hm
  have hlower : ∀ x ∈ Set.uIcc
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b),
      Complex.logarithmicPhaseEnhancedPositiveModeGap t b m ≤
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ :=
    fun x hx =>
      Complex.logarithmicPhaseEnhancedPositiveModeDerivative_gap
        t a b m ha hab hm hx
  unfold Complex.logarithmicPhaseEnhancedPositiveModeClosedMajorant
  exact Complex.norm_logarithmicPhaseAdaptedPacket_le_closedMajorant
    t a b m (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)
    ha hab hgap hlower

end
end LFunctions
end Boundary
