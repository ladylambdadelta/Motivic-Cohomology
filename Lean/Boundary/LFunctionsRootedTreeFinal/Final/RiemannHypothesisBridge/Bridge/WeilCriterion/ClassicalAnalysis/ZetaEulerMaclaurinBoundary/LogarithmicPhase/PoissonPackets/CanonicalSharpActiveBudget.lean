import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalSharpStationaryPacket
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalActiveBudget

/-!
# Sharp active-family logarithmic packet budget

This file sums the sharp canonical packet estimate over the finite interior
mode family.  Separate finite sums are exposed for cutoff crossings, left
tails, central windows, and right tails.  That separation is the interface
needed by the arithmetic owner: cardinality controls crossings and windows,
while the reciprocal-gap sums retain their mode dependence.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Sum of the fixed crossing budget over canonical interior modes. -/
def Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ _m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
    (4 / 3 : ℝ)

/-- Sum of sharp canonical left-tail budgets. -/
def Complex.logarithmicPhasePoissonCanonicalSharpLeftTailSum
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
    Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget t m

/-- Sum of canonical central-window widths. -/
def Complex.logarithmicPhasePoissonCanonicalSharpCentralWindowSum
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
    Complex.logarithmicPhasePoissonCanonicalWindowWidth t m

/-- Sum of sharp canonical right-tail budgets. -/
def Complex.logarithmicPhasePoissonCanonicalSharpRightTailSum
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
    Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget t m

/-- Four-component sharp budget for all canonical interior modes. -/
def Complex.logarithmicPhasePoissonCanonicalSharpInteriorBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget t a b +
    Complex.logarithmicPhasePoissonCanonicalSharpLeftTailSum t a b +
      Complex.logarithmicPhasePoissonCanonicalSharpCentralWindowSum t a b +
        Complex.logarithmicPhasePoissonCanonicalSharpRightTailSum t a b

theorem Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget
  exact Finset.sum_nonneg
    (fun m hm => div_nonneg (OfNat.zero_le 4) (OfNat.zero_le 3))

theorem Complex.logarithmicPhasePoissonCanonicalSharpCentralWindowSum_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalSharpCentralWindowSum t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpCentralWindowSum
  exact Finset.sum_nonneg
    (fun m hm =>
      Complex.logarithmicPhasePoissonCanonicalWindowWidth_nonneg t m)

theorem Complex.logarithmicPhasePoissonCanonicalSharpLeftTailSum_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalSharpLeftTailSum t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpLeftTailSum
  exact Finset.sum_nonneg (fun m hm => by
    have hmem :=
      (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
        t a b m).mp hm
    have hleftPos :=
      Complex.logarithmicPhasePoissonCanonicalWindowLeft_pos_of_mem
        t ht ha hm
    exact
      Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget_nonneg
        t ht hmem.2.1 hleftPos)

theorem Complex.logarithmicPhasePoissonCanonicalSharpRightTailSum_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalSharpRightTailSum t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpRightTailSum
  exact Finset.sum_nonneg (fun m hm => by
    have hmem :=
      (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
        t a b m).mp hm
    exact
      Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget_nonneg
        t ht hmem.2.1)

theorem Complex.logarithmicPhasePoissonCanonicalSharpInteriorBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalSharpInteriorBudget t a b := by
  exact
    add_nonneg
      (add_nonneg
        (add_nonneg
          (Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget_nonneg
            t a b)
          (Complex.logarithmicPhasePoissonCanonicalSharpLeftTailSum_nonneg
            t ht a b ha))
        (Complex.logarithmicPhasePoissonCanonicalSharpCentralWindowSum_nonneg
          t a b))
      (Complex.logarithmicPhasePoissonCanonicalSharpRightTailSum_nonneg
        t ht a b)

/-- Sum of the per-mode sharp stationary majorants equals the named
four-component active budget. -/
theorem Complex.sum_logarithmicPhasePoissonCanonicalSharpStationaryMajorant_eq_budget
    (t : ℝ) (a b : ℤ) :
    (∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
      Complex.logarithmicPhasePoissonCanonicalSharpStationaryMajorant
        t a b m) =
      Complex.logarithmicPhasePoissonCanonicalSharpInteriorBudget t a b := by
  let modes :=
    Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b
  let crossing : ℤ → ℝ := fun _m => 4 / 3
  let leftTail : ℤ → ℝ := fun m =>
    Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget t m
  let central : ℤ → ℝ := fun m =>
    Complex.logarithmicPhasePoissonCanonicalWindowWidth t m
  let rightTail : ℤ → ℝ := fun m =>
    Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget t m
  have hfirst :
      (∑ m ∈ modes,
        crossing m + leftTail m + central m + rightTail m) =
        (∑ m ∈ modes, crossing m + leftTail m + central m) +
          ∑ m ∈ modes, rightTail m := by
    exact Finset.sum_add_distrib
  have hsecond :
      (∑ m ∈ modes, crossing m + leftTail m + central m) =
        (∑ m ∈ modes, crossing m + leftTail m) +
          ∑ m ∈ modes, central m := by
    exact Finset.sum_add_distrib
  have hthird :
      (∑ m ∈ modes, crossing m + leftTail m) =
        (∑ m ∈ modes, crossing m) +
          ∑ m ∈ modes, leftTail m := by
    exact Finset.sum_add_distrib
  calc
    (∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
      Complex.logarithmicPhasePoissonCanonicalSharpStationaryMajorant
        t a b m) =
        ∑ m ∈ modes,
          crossing m + leftTail m + central m + rightTail m := by
      rfl
    _ =
        (∑ m ∈ modes, crossing m + leftTail m + central m) +
          ∑ m ∈ modes, rightTail m := hfirst
    _ =
        ((∑ m ∈ modes, crossing m + leftTail m) +
          ∑ m ∈ modes, central m) +
            ∑ m ∈ modes, rightTail m := by
      exact congrArg
        (fun value : ℝ => value + ∑ m ∈ modes, rightTail m)
        hsecond
    _ =
        (((∑ m ∈ modes, crossing m) +
          ∑ m ∈ modes, leftTail m) +
            ∑ m ∈ modes, central m) +
              ∑ m ∈ modes, rightTail m := by
      exact congrArg
        (fun value : ℝ =>
          (value + ∑ m ∈ modes, central m) +
            ∑ m ∈ modes, rightTail m)
        hthird
    _ =
        Complex.logarithmicPhasePoissonCanonicalSharpInteriorBudget
          t a b := by
      rfl

/-- The actual finite sum of interior packet norms is bounded by the sharp
four-component budget. -/
theorem Complex.logarithmicPhasePoissonCanonicalInteriorNormSum_le_sharpBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b,
      ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖) ≤
      Complex.logarithmicPhasePoissonCanonicalSharpInteriorBudget t a b := by
  have hpointwise :=
    Finset.sum_le_sum (fun m hm =>
      Complex.norm_integerBlockFourierPacket_le_canonicalSharpStationaryMajorant
        t ht ht_nonneg a b m ha hab hm)
  exact le_trans hpointwise
    (le_of_eq
      (Complex.sum_logarithmicPhasePoissonCanonicalSharpStationaryMajorant_eq_budget
        t a b))

/-- The interior packet `tsum` is bounded by the sharp active budget. -/
theorem Complex.norm_logarithmicPhasePoissonCanonicalInterior_packet_tsum_le_sharpBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalSharpInteriorBudget t a b := by
  have hnormSum :=
    Complex.norm_logarithmicPhasePoissonCanonicalInterior_packet_tsum_le_sum
      t a b
  have hsharp :=
    Complex.logarithmicPhasePoissonCanonicalInteriorNormSum_le_sharpBudget
      t ht ht_nonneg a b ha hab
  exact le_trans hnormSum hsharp

/-- The crossing component is exactly cardinality times `4/3`. -/
theorem Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget_eq_card_mul
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget t a b =
      ((Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b).card : ℝ) *
        (4 / 3 : ℝ) := by
  unfold Complex.logarithmicPhasePoissonCanonicalSharpCrossingBudget
  exact
    Finset.sum_const_real_eq_card_mul
      (Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b)
      (4 / 3)

end

end LFunctions
end Boundary
