import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePacketBounds

/-!
# Finite quantitative packet budgets

This owner converts pointwise packet estimates into finite Fourier-mode
budgets for the fixed-collar quantitative reconstruction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_norm_sum
    (t : ℝ)
    (a b : ℤ)
    (modes : Finset ℤ) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ modes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ := by
  have hfinite :=
    modes.tsum_subtype
      (fun m : ℤ => Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤
        ∑ m ∈ modes,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
      hfinite.symm
      (norm_sum_le modes
        (fun m : ℤ => Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))

theorem Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_majorant_sum
    (t : ℝ)
    (a b : ℤ)
    (modes : Finset ℤ)
    (bound : ℤ → ℝ)
    (hbound : ∀ m ∈ modes,
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤ bound m) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ modes, bound m := by
  have hnorm :=
    Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_norm_sum
      t a b modes
  have hsum :
      (∑ m ∈ modes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖) ≤
        ∑ m ∈ modes, bound m := by
    exact Finset.sum_le_sum (fun m hm => hbound m hm)
  exact le_trans hnorm hsum

theorem Complex.norm_logarithmicPhaseQuantitative_leftInactivePacket_tsum_le_explicit_sum
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (modes : Finset ℤ)
    (hleft : ∀ m ∈ modes,
      m < 0 ∧ Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ)) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ modes,
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
      t a b modes
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
        Complex.norm_logarithmicPhaseQuantitativePacket_le_leftInactive_explicit
          t ht ht_nonneg a b m ha hab (hleft m hm).1 (hleft m hm).2)

theorem Complex.norm_logarithmicPhaseQuantitative_rightInactivePacket_tsum_le_explicit_sum
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (modes : Finset ℤ)
    (hright : ∀ m ∈ modes,
      m < 0 ∧ (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ modes,
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
      t a b modes
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
        Complex.norm_logarithmicPhaseQuantitativePacket_le_rightInactive_explicit
          t ht ht_nonneg a b m ha hab (hright m hm).1 (hright m hm).2)

def Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
    (t : ℝ)
    (a b m : ℤ)
    (radius : ℝ) : ℝ :=
  2 / 3 +
    (2 * ((2 * Real.pi * (-(m : ℝ))) *
      (Complex.logarithmicPhaseFourierStationaryPoint t m -
        (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) /
        (Complex.logarithmicPhaseFourierStationaryPoint t m - radius))⁻¹ +
      ((Complex.logarithmicPhaseFourierStationaryPoint t m - radius) - (a : ℝ)) •
        ((‖t‖ / (a : ℝ) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m -
              (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) /
            (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) ^ 2)) +
    ((Complex.logarithmicPhaseFourierStationaryPoint t m + radius) -
      (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) +
    (2 * ((2 * Real.pi * (-(m : ℝ))) *
      ((Complex.logarithmicPhaseFourierStationaryPoint t m + radius) -
        Complex.logarithmicPhaseFourierStationaryPoint t m) /
        (b : ℝ))⁻¹ +
      ((b : ℝ) - (Complex.logarithmicPhaseFourierStationaryPoint t m + radius)) •
        ((‖t‖ / (Complex.logarithmicPhaseFourierStationaryPoint t m + radius) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            ((Complex.logarithmicPhaseFourierStationaryPoint t m + radius) -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (b : ℝ)) ^ 2))

theorem Complex.norm_logarithmicPhaseQuantitative_interiorActivePacket_tsum_le_explicit_sum
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑' m :
        {m : ℤ // m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound t a b m radius := by
  let modes := Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius
  have hbound : ∀ m ∈ modes,
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound t a b m radius := by
    intro m hm
    have hmem :=
      (Complex.mem_logarithmicPhasePoissonInteriorActiveModes_iff t a b m radius).mp hm
    exact
      Complex.norm_logarithmicPhaseQuantitativePacket_le_active_stationary_explicit
        t ht ht_nonneg a b m ha hab hmem.2.1
        (Complex.logarithmicPhaseFourierStationaryPoint t m) radius rfl hradius
        hmem.2.2.1 hmem.2.2.2
  exact
    Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_majorant_sum
      t a b modes
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound t a b m radius)
      hbound

theorem Complex.norm_logarithmicPhaseQuantitative_activePacket_tsum_le_interior_add_endpoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound t a b m radius +
      ∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ := by
  let active := Complex.logarithmicPhasePoissonActiveModes t a b
  let interior := Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius
  let endpoint := Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius
  have hsubset : (interior : Set ℤ) ⊆ (active : Set ℤ) :=
    Complex.logarithmicPhasePoissonInteriorActiveModes_subset_activeModes
      t a b radius (le_of_lt hradius)
  have hunion : interior ∪ endpoint = active := by
    change
      Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius ∪
          Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius =
        Complex.logarithmicPhasePoissonActiveModes t a b
    exact
      Complex.logarithmicPhasePoissonInterior_union_endpoint_eq_active
        t a b radius hsubset
  have hdisjoint : Disjoint interior endpoint := Finset.disjoint_sdiff
  let packet : ℤ → ℂ :=
    fun m => Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m
  have hactive_tsum := active.tsum_subtype packet
  have hinterior_tsum := interior.tsum_subtype packet
  have hendpoint_tsum := endpoint.tsum_subtype packet
  have hsum :
      (∑ m ∈ active, packet m) =
        (∑ m ∈ interior, packet m) + ∑ m ∈ endpoint, packet m := by
    exact
      Eq.trans
        (congrArg (fun modes : Finset ℤ => ∑ m ∈ modes, packet m) hunion.symm)
        (Finset.sum_union hdisjoint)
  have hdecomposition :
      (∑' m : {m : ℤ // m ∈ active}, packet m) =
        (∑' m : {m : ℤ // m ∈ interior}, packet m) +
          ∑' m : {m : ℤ // m ∈ endpoint}, packet m := by
    exact
      Eq.trans
        (hactive_tsum.trans hsum)
        (congrArg₂ (fun left right : ℂ => left + right)
          hinterior_tsum.symm hendpoint_tsum.symm)
  have hinterior_bound :=
    Complex.norm_logarithmicPhaseQuantitative_interiorActivePacket_tsum_le_explicit_sum
      t ht ht_nonneg a b ha hab radius hradius
  have hendpoint_bound :=
    Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_norm_sum
      t a b endpoint
  calc
    ‖∑' m : {m : ℤ // m ∈ active}, packet m‖ =
        ‖(∑' m : {m : ℤ // m ∈ interior}, packet m) +
          ∑' m : {m : ℤ // m ∈ endpoint}, packet m‖ :=
      congrArg norm hdecomposition
    _ ≤
        ‖∑' m : {m : ℤ // m ∈ interior}, packet m‖ +
          ‖∑' m : {m : ℤ // m ∈ endpoint}, packet m‖ := norm_add_le _ _
    _ ≤
        (∑ m ∈ interior,
          Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound t a b m radius) +
          ∑ m ∈ endpoint,
            ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ :=
      add_le_add hinterior_bound hendpoint_bound

end
end LFunctions
end Boundary
