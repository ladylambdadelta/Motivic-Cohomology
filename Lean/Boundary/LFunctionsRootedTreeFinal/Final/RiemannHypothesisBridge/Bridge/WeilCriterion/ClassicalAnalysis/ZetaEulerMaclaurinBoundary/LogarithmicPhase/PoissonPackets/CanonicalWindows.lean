import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Budgets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.DirectBudget

/-!
# Canonical mode-dependent stationary windows

For logarithmic packets the natural central radius is `sqrt x_m`, where
`x_m` is the corrected Fourier stationary point.  It varies with the mode.
This file owns that geometry and the finite summation of the resulting exact
per-packet stationary bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonCanonicalRadius
    (t : ℝ) (m : ℤ) : ℝ :=
  Real.sqrt (Complex.logarithmicPhaseFourierStationaryPoint t m)

theorem Complex.logarithmicPhasePoissonCanonicalRadius_nonneg
    (t : ℝ) (m : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalRadius
  exact Real.sqrt_nonneg _

theorem Complex.logarithmicPhasePoissonCanonicalRadius_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 < Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalRadius
  exact
    Real.sqrt_pos.mpr
      (Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm)

theorem Complex.logarithmicPhasePoissonCanonicalRadius_sq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePoissonCanonicalRadius t m *
        Complex.logarithmicPhasePoissonCanonicalRadius t m =
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalRadius
  exact
    Real.mul_self_sqrt
      (le_of_lt
        (Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm))

def Complex.logarithmicPhasePoissonCanonicalInteriorModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonModeRange t a).filter
    (fun m : ℤ =>
      m < 0 ∧
        (a : ℝ) ≤
          Complex.logarithmicPhaseFourierStationaryPoint t m -
            Complex.logarithmicPhasePoissonCanonicalRadius t m ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m +
            Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
          (b : ℝ))

theorem Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonModeRange t a ∧
        m < 0 ∧
          (a : ℝ) ≤
            Complex.logarithmicPhaseFourierStationaryPoint t m -
              Complex.logarithmicPhasePoissonCanonicalRadius t m ∧
          Complex.logarithmicPhaseFourierStationaryPoint t m +
              Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
            (b : ℝ) := by
  exact Finset.mem_filter

theorem Complex.logarithmicPhasePoissonCanonicalInteriorModes_subset_modeRange
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b ⊆
      Complex.logarithmicPhasePoissonModeRange t a := by
  exact Finset.filter_subset _ _

theorem Complex.logarithmicPhasePoissonCanonicalInteriorModes_card_le_modeRange_card
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b).card ≤
      (Complex.logarithmicPhasePoissonModeRange t a).card := by
  exact
    Finset.card_le_card
      (Complex.logarithmicPhasePoissonCanonicalInteriorModes_subset_modeRange
        t a b)

theorem Complex.logarithmicPhasePoissonCanonicalRadius_left_lt_center
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhasePoissonCanonicalRadius t m <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  exact
    sub_lt_self _
      (Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hm)

theorem Complex.logarithmicPhasePoissonCanonicalRadius_center_lt_right
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m <
      Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  exact
    lt_add_of_pos_right _
      (Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hm)

theorem Complex.norm_integerBlockFourierPacket_le_canonical_stationary_bound
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m
        (Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hradius :
      0 < Complex.logarithmicPhasePoissonCanonicalRadius t m :=
    Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hmem.2.1
  exact
    Complex.norm_integerBlockFourierPacket_le_active_stationary_explicit
      t ht ht_nonneg a b m ha hab hmem.2.1
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhasePoissonCanonicalRadius t m)
      rfl hradius hmem.2.2.1 hmem.2.2.2

theorem Complex.norm_logarithmicPhasePoissonCanonicalInterior_packet_tsum_le_sum
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
        Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m
          (Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
  let modes := Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b
  let bound : ℤ → ℝ :=
    fun m : ℤ =>
      Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m
        (Complex.logarithmicPhasePoissonCanonicalRadius t m)
  have hbound : ∀ m ∈ modes,
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ bound m := by
    intro m hm
    exact
      Complex.norm_integerBlockFourierPacket_le_canonical_stationary_bound
        t ht ht_nonneg a b m ha hab hm
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b modes bound hbound

def Complex.logarithmicPhasePoissonCanonicalInteriorBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
    Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m
      (Complex.logarithmicPhasePoissonCanonicalRadius t m)

theorem Complex.logarithmicPhasePoissonCanonicalInteriorBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalInteriorBudget
  exact
    Finset.sum_nonneg
      (fun m hm => by
        have hpacket :=
          Complex.norm_integerBlockFourierPacket_le_canonical_stationary_bound
            t ht ht_nonneg a b m ha hab hm
        exact le_trans (norm_nonneg _) hpacket)

theorem Complex.norm_logarithmicPhasePoissonCanonicalInterior_packet_tsum_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b := by
  exact
    Complex.norm_logarithmicPhasePoissonCanonicalInterior_packet_tsum_le_sum
      t ht ht_nonneg a b ha hab

theorem Complex.logarithmicPhasePoissonCanonicalInteriorBudget_upper_of_pointwise_bound
    (t : ℝ) (a b : ℤ) (C : ℝ)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b →
          Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m
            (Complex.logarithmicPhasePoissonCanonicalRadius t m) ≤ C) :
    Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b ≤
      ((Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b).card : ℝ) * C := by
  unfold Complex.logarithmicPhasePoissonCanonicalInteriorBudget
  have hpointwise :=
    Finset.sum_le_sum
      (fun m hm => hbound m hm)
  have hconstant :
      (∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
        C) =
        ((Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b).card : ℝ) * C := by
    exact
      Finset.sum_const_real_eq_card_mul
        (Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) C
  exact hpointwise.trans_eq hconstant

theorem Complex.logarithmicPhasePoissonCanonicalInteriorBudget_le_modeRange_card_mul
    (t : ℝ) (a b : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b →
          Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m
            (Complex.logarithmicPhasePoissonCanonicalRadius t m) ≤ C) :
    Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b ≤
      ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) * C := by
  have hbudget :=
    Complex.logarithmicPhasePoissonCanonicalInteriorBudget_upper_of_pointwise_bound
      t a b C hbound
  have hcard :
      ((Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Nat.cast_le.mpr
      (Complex.logarithmicPhasePoissonCanonicalInteriorModes_card_le_modeRange_card
        t a b)
  exact le_trans hbudget (mul_le_mul_of_nonneg_right hcard hC)

end
end LFunctions
end Boundary
