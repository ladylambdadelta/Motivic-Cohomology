import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeEndpointPartition

/-!
# Quantitative endpoint-collar packets

The endpoint-active collar classes have stationary centers outside the
principal interval, hence they are quantitatively nonstationary on that
interval and use the established left/right tail packet estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointLeftCollarPacket_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hm : m ∈ Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      2 / 3 +
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (b : ℝ))⁻¹ +
        ((b : ℝ) - (a : ℝ)) •
          ((‖t‖ / (a : ℝ) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                (b : ℝ)) ^ 2) := by
  have hdata :=
    (Complex.mem_logarithmicPhaseQuantitativeEndpointLeftCollarModes_iff
      t a b m radius).mp hm
  have hactive_data := Finset.mem_sdiff.mp hdata.1
  have hmode :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mp hactive_data.1
  exact
    Complex.norm_logarithmicPhaseQuantitativePacket_le_leftInactive_explicit
      t ht ht_nonneg a b m ha hab hmode.2.1 hdata.2

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointRightCollarPacket_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hm : m ∈ Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      2 / 3 +
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
            (b : ℝ))⁻¹ +
        ((b : ℝ) - (a : ℝ)) •
          ((‖t‖ / (a : ℝ) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
                (b : ℝ)) ^ 2) := by
  have hdata :=
    (Complex.mem_logarithmicPhaseQuantitativeEndpointRightCollarModes_iff
      t a b m radius).mp hm
  have hactive_data := Finset.mem_sdiff.mp hdata.1
  have hmode :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mp hactive_data.1
  exact
    Complex.norm_logarithmicPhaseQuantitativePacket_le_rightInactive_explicit
      t ht ht_nonneg a b m ha hab hmode.2.1 hdata.2

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointLeftCollar_tsum_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ) :
    ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius,
        (2 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                  (b : ℝ)) ^ 2)) := by
  exact
    Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_majorant_sum
      t a b (Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius)
      (fun m : ℤ =>
        2 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                  (b : ℝ)) ^ 2))
      (fun m hm =>
        Complex.norm_logarithmicPhaseQuantitativeEndpointLeftCollarPacket_le
          t ht ht_nonneg a b m ha hab radius hm)

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointRightCollar_tsum_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ) :
    ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius,
        (2 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
                  (b : ℝ)) ^ 2)) := by
  exact
    Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_majorant_sum
      t a b (Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius)
      (fun m : ℤ =>
        2 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
                  (b : ℝ)) ^ 2))
      (fun m hm =>
        Complex.norm_logarithmicPhaseQuantitativeEndpointRightCollarPacket_le
          t ht ht_nonneg a b m ha hab radius hm)

end
end LFunctions
end Boundary
