import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalActiveBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.DirectBudget

/-!
# Global logarithmic Poisson budget with canonical windows

This owner combines the mode-dependent active stationary decomposition with
the pre-existing non-active frequency family.  It is the canonical direct
Poisson block budget consumed by the later arithmetic closure.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b +
    Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b +
      Complex.logarithmicPhasePoissonInactiveBudget t a b

theorem Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget
  exact
    add_nonneg
      (add_nonneg
        (Complex.logarithmicPhasePoissonCanonicalInteriorBudget_nonneg
          t ht ht_nonneg a b ha hab)
        (Complex.logarithmicPhasePoissonCanonicalEndpointBudget_nonneg t a b))
      (Complex.logarithmicPhasePoissonInactiveBudget_nonneg t a b)

theorem Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_le_canonicalThreeComponentBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget t a b := by
  have hsplit :=
    Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_active_add_nonactive_tsum_norm
      t a b ha hab
  have hactive :=
    Complex.logarithmicPhasePoissonCanonicalActive_packet_tsum_le_interior_add_endpoint
      t ht ht_nonneg a b ha hab
  exact
    le_trans hsplit
      (add_le_add_right hactive
        (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖))

theorem Complex.logarithmicPhase_integerBlock_norm_le_canonicalThreeComponentBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget t a b := by
  have hreconstruction :=
    Complex.logarithmicPhase_integerBlock_poisson_packet_reconstruction
      t a b ha hab
  have hpacket :=
    Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_le_canonicalThreeComponentBudget
      t ht ht_nonneg a b ha hab
  calc
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ =
        ‖∑' m : ℤ,
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ :=
      congrArg norm hreconstruction
    _ ≤ Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget t a b :=
      hpacket

theorem Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget_upper_of_components
    (t : ℝ) (a b : ℤ) (I E N : ℝ)
    (hinterior :
      Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b ≤ I)
    (hendpoint :
      Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b ≤ E)
    (hinactive :
      Complex.logarithmicPhasePoissonInactiveBudget t a b ≤ N) :
    Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget t a b ≤
      I + E + N := by
  unfold Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget
  exact
    add_le_add
      (add_le_add hinterior hendpoint)
      hinactive

theorem Complex.logarithmicPhase_integerBlock_norm_le_of_canonicalPoisson_components
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (I E N : ℝ)
    (hinterior :
      Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b ≤ I)
    (hendpoint :
      Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b ≤ E)
    (hinactive :
      Complex.logarithmicPhasePoissonInactiveBudget t a b ≤ N) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      I + E + N := by
  have hpacket :=
    Complex.logarithmicPhase_integerBlock_norm_le_canonicalThreeComponentBudget
      t ht ht_nonneg a b ha hab
  have hcomponents :=
    Complex.logarithmicPhasePoissonCanonicalThreeComponentBudget_upper_of_components
      t a b I E N hinterior hendpoint hinactive
  exact le_trans hpacket hcomponents

end
end LFunctions
end Boundary
