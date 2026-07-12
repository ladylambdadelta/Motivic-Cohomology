import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedComplementAssembly

/-!
# Complete phase-adapted three-component packet estimate

The existing active interior/endpoint estimate is combined with the new
finite-inactive and phase-adapted infinite-tail complement estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_adaptedThreeComponent
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseAdaptedThreeComponentBudget
        t a b radius := by
  have hcomplement :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_adaptedComplement
      t a b ha hab
  have hactive :=
    Complex.norm_logarithmicPhaseQuantitativeActivePacket_tsum_le_two_components
      t ht htNonneg a b ha hab radius hradius
  unfold Complex.logarithmicPhaseAdaptedThreeComponentBudget
  exact le_trans hcomplement
    (add_le_add_right hactive
      (Complex.logarithmicPhaseAdaptedComplementBudget t a b))

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_adaptedThreeComponent
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      Complex.logarithmicPhaseAdaptedThreeComponentBudget
        t a b radius := by
  have hreconstruction :=
    Complex.logarithmicPhase_quantitativeBlock_poisson_packet_reconstruction
      t a b ha hab
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_adaptedThreeComponent
      t ht htNonneg a b ha hab radius hradius
  exact le_trans (le_of_eq (congrArg norm hreconstruction)) hpacket

end
end LFunctions
end Boundary
