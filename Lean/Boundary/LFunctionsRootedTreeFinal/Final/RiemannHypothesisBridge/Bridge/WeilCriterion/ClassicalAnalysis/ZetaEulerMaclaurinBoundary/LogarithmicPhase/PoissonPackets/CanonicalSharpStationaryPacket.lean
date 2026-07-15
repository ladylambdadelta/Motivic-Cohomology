import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.SharpMonotoneStationaryTails
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalTails

/-!
# Canonical sharp logarithmic stationary packet

This file replaces the coarse interval-length times curvature remainder by the
exact monotone reciprocal-gap tails.  The central interval remains bounded by
its geometric width.  The resulting packet majorant has the natural
stationary-phase shape: two near-edge reciprocal gaps, one square-root central
window, and the fixed cutoff-crossing budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Sharp left-tail budget at the canonical left window endpoint. -/
def Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseLeftReciprocalGap t m
      (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) +
    Complex.logarithmicPhaseLeftReciprocalGap t m
      (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m)

/-- Sharp right-tail budget at the canonical right window endpoint. -/
def Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseRightReciprocalGap t m
      (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) +
    Complex.logarithmicPhaseRightReciprocalGap t m
      (Complex.logarithmicPhasePoissonCanonicalWindowRight t m)

/-- Sharp canonical stationary-packet majorant. -/
def Complex.logarithmicPhasePoissonCanonicalSharpStationaryMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  4 / 3 +
    Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget t m +
      Complex.logarithmicPhasePoissonCanonicalWindowWidth t m +
        Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget t m

theorem Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    (hleft :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget t m := by
  have hcenter :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m <
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowLeft
    exact
      Complex.logarithmicPhasePoissonCanonicalRadius_left_lt_center
        t ht hm
  have hcoefficient :=
    Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
      t ht m hm hleft hcenter
  have hterm :
      0 ≤ Complex.logarithmicPhaseLeftReciprocalGap t m
        (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) := by
    exact Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      hcoefficient.symm
      (norm_nonneg _)
  exact add_nonneg hterm hterm

theorem Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget t m := by
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hrightPos :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowRight t m :=
    lt_of_lt_of_le hcenterPos
      (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m)
  have hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m <
        Complex.logarithmicPhasePoissonCanonicalWindowRight t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowRight
    exact
      Complex.logarithmicPhasePoissonCanonicalRadius_center_lt_right
        t ht hm
  have hcoefficient :=
    Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
      t ht m hm hrightPos hcenter
  have hterm :
      0 ≤ Complex.logarithmicPhaseRightReciprocalGap t m
        (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) := by
    exact Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      hcoefficient.symm
      (norm_nonneg _)
  exact add_nonneg hterm hterm

/-- Sharp left-tail estimate at the canonical square-root window. -/
theorem Complex.norm_logarithmicPhasePoissonCanonicalLeftTail_le_sharp
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalLeftTail t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalSharpLeftTailBudget t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem
      t a b m hm
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hleftRight :
      (a : ℝ) ≤ Complex.logarithmicPhasePoissonCanonicalWindowLeft t m :=
    hbounds.1
  have hcenter :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m <
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowLeft
    exact
      Complex.logarithmicPhasePoissonCanonicalRadius_left_lt_center
        t ht hmem.2.1
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_leftOfStationary_le_twice_reciprocalGap
      t ht ht_nonneg m hmem.2.1
      (a : ℝ)
      (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m)
      haPos hleftRight hcenter

/-- Sharp right-tail estimate at the canonical square-root window. -/
theorem Complex.norm_logarithmicPhasePoissonCanonicalRightTail_le_sharp
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalRightTail t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalSharpRightTailBudget t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem
      t a b m hm
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hleftPos :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowRight t m :=
    lt_of_lt_of_le haPos
      (le_trans hbounds.1
        (le_trans
          (Complex.logarithmicPhasePoissonCanonicalWindowLeft_le_center t m)
          (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m)))
  have hleftRight :
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m ≤ (b : ℝ) :=
    hbounds.2
  have hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m <
        Complex.logarithmicPhasePoissonCanonicalWindowRight t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowRight
    exact
      Complex.logarithmicPhasePoissonCanonicalRadius_center_lt_right
        t ht hmem.2.1
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_rightOfStationary_le_twice_reciprocalGap
      t ht ht_nonneg m hmem.2.1
      (Complex.logarithmicPhasePoissonCanonicalWindowRight t m)
      (b : ℝ) hleftPos hleftRight hcenter

/-- Complete sharp canonical packet bound, including both cutoff crossings. -/
theorem Complex.norm_integerBlockFourierPacket_le_canonicalSharpStationaryMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalSharpStationaryMajorant
        t a b m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem
      t a b m hm
  have hradiusNonneg :=
    Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m
  have hcenterOrder :
      Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m +
          Complex.logarithmicPhasePoissonCanonicalRadius t m :=
    le_trans
      (Complex.logarithmicPhasePoissonCanonicalWindowLeft_le_center t m)
      (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m)
  have hleft :=
    Complex.norm_logarithmicPhasePoissonCanonicalLeftTail_le_sharp
      t ht ht_nonneg a b m ha hm
  have hright :=
    Complex.norm_logarithmicPhasePoissonCanonicalRightTail_le_sharp
      t ht ht_nonneg a b m ha hm
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_active_three_piece
      t ht_nonneg a b m ha hab
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhasePoissonCanonicalRadius t m)
      hbounds.1 hcenterOrder hbounds.2
      hleft hright hradiusNonneg
  exact hpacket

end

end LFunctions
end Boundary
