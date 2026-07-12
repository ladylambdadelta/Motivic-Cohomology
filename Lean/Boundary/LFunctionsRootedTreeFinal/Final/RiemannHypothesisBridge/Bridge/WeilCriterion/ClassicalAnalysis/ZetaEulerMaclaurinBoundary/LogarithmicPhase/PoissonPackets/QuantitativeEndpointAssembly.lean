import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeEndpointInternal

/-!
# Exact quantitative endpoint-active sum decomposition

The endpoint-active Fourier sum is the disjoint sum of its left-collar,
internal clipped, and right-collar subfamilies.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointActive_tsum_le_three_parts
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ)
    (hab : a ≤ b) :
    ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
        ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
        ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ := by
  let left := Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius
  let internal := Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius
  let right := Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius
  let endpoint := Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius
  let packet : ℤ → ℂ :=
    fun m => Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m
  have hleft_internal :=
    Complex.logarithmicPhaseQuantitativeEndpointLeft_disjoint_internal t a b radius
  have hleft_internal_right :=
    Complex.logarithmicPhaseQuantitativeEndpointLeftInternal_disjoint_right
      t a b radius hab
  have hunion :=
    Complex.logarithmicPhaseQuantitativeEndpointLocation_union_eq_endpoint
      t a b radius hab
  have hleft_tsum := left.tsum_subtype packet
  have hinternal_tsum := internal.tsum_subtype packet
  have hright_tsum := right.tsum_subtype packet
  have hendpoint_tsum := endpoint.tsum_subtype packet
  have hleft_internal_sum :
      (∑ m ∈ left ∪ internal, packet m) =
        (∑ m ∈ left, packet m) + ∑ m ∈ internal, packet m :=
    Finset.sum_union hleft_internal
  have htotal_sum :
      (∑ m ∈ endpoint, packet m) =
        ((∑ m ∈ left, packet m) + ∑ m ∈ internal, packet m) +
          ∑ m ∈ right, packet m := by
    calc
      (∑ m ∈ endpoint, packet m) =
          ∑ m ∈ (left ∪ internal) ∪ right, packet m :=
        congrArg (fun modes : Finset ℤ => ∑ m ∈ modes, packet m) hunion.symm
      _ = (∑ m ∈ left ∪ internal, packet m) + ∑ m ∈ right, packet m :=
        Finset.sum_union hleft_internal_right
      _ = ((∑ m ∈ left, packet m) + ∑ m ∈ internal, packet m) +
          ∑ m ∈ right, packet m :=
        congrArg (fun value : ℂ => value + ∑ m ∈ right, packet m)
          hleft_internal_sum
  have hdecomposition :
      (∑' m : {m : ℤ // m ∈ endpoint}, packet m) =
        ((∑' m : {m : ℤ // m ∈ left}, packet m) +
          ∑' m : {m : ℤ // m ∈ internal}, packet m) +
          ∑' m : {m : ℤ // m ∈ right}, packet m := by
    exact
      Eq.trans
        (hendpoint_tsum.trans htotal_sum)
        (congrArg₂ (fun leftPart rightPart : ℂ => leftPart + rightPart)
          (congrArg₂ (fun leftPart internalPart : ℂ => leftPart + internalPart)
            hleft_tsum.symm hinternal_tsum.symm)
          hright_tsum.symm)
  calc
    ‖∑' m : {m : ℤ // m ∈ endpoint}, packet m‖ =
        ‖((∑' m : {m : ℤ // m ∈ left}, packet m) +
          ∑' m : {m : ℤ // m ∈ internal}, packet m) +
          ∑' m : {m : ℤ // m ∈ right}, packet m‖ :=
      congrArg norm hdecomposition
    _ ≤
        ‖(∑' m : {m : ℤ // m ∈ left}, packet m) +
          ∑' m : {m : ℤ // m ∈ internal}, packet m‖ +
          ‖∑' m : {m : ℤ // m ∈ right}, packet m‖ := norm_add_le _ _
    _ ≤
        (‖∑' m : {m : ℤ // m ∈ left}, packet m‖ +
          ‖∑' m : {m : ℤ // m ∈ internal}, packet m‖) +
          ‖∑' m : {m : ℤ // m ∈ right}, packet m‖ :=
      add_le_add_right (norm_add_le _ _) _

end
end LFunctions
end Boundary
