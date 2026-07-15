import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessEndpointCenterLayers
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.ModeRangeCore

/-!
# Frequency layers for balanced endpoint modes

This owner transports each explicit center layer through the antitone map
`x ↦ ‖t‖/(2πx)`.  The resulting intervals contain the positive integer
coordinate `-m`; their reflected intervals contain `(m : ℝ)` and are ready for
the generic short-interval packing theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessLeftOutsideFrequencyLower
    (t : ℝ) (a : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t (a : ℝ)

def Complex.logarithmicPhaseBProcessLeftOutsideFrequencyUpper
    (t : ℝ) (a : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t
    (Real.integerBlockCutoffSupportLeftEndpoint a)

def Complex.logarithmicPhaseBProcessRightOutsideFrequencyLower
    (t : ℝ) (b : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t ((b : ℝ) + 2 / 3)

def Complex.logarithmicPhaseBProcessRightOutsideFrequencyUpper
    (t : ℝ) (b : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t (b : ℝ)

def Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower
    (t : ℝ) (a : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t
    (Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t a)

def Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper
    (t : ℝ) (a : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t (a : ℝ)

def Complex.logarithmicPhaseBProcessRightClippedFrequencyLower
    (t : ℝ) (b : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t (b : ℝ)

def Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper
    (t : ℝ) (b : ℤ) : ℝ :=
  Complex.logarithmicPhaseCenterFrequencyCoordinate t
    (Complex.logarithmicPhaseBProcessRightClippedCenterLower t b)

theorem Complex.logarithmicPhaseBProcessLeftOutside_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b) :
    Complex.logarithmicPhaseBProcessLeftOutsideFrequencyLower t a ≤ -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseBProcessLeftOutsideFrequencyUpper t a := by
  have hclass :
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) :=
    (Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
      t a b m).mp hm
  have hmNeg : m < 0 :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hclass.1
  have hcenters :
      Real.integerBlockCutoffSupportLeftEndpoint a ≤
          Complex.logarithmicPhaseFourierStationaryPoint t m ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (a : ℝ) :=
    Complex.logarithmicPhaseBProcessLeftOutside_center_bounds t a b hm
  have hleftPos : 0 < Real.integerBlockCutoffSupportLeftEndpoint a :=
    Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  exact
    Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
      t ht hmNeg hleftPos hcenters.1 hcenters.2

theorem Complex.logarithmicPhaseBProcessRightOutside_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (hb : 1 ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b) :
    Complex.logarithmicPhaseBProcessRightOutsideFrequencyLower t b ≤ -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseBProcessRightOutsideFrequencyUpper t b := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
      t a b m).mp hm
  have hmNeg : m < 0 :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hclass.1
  have hcenters :
      (b : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m ≤
          (b : ℝ) + 2 / 3 :=
    Complex.logarithmicPhaseBProcessRightOutside_center_bounds t a b hm
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  exact
    Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
      t ht hmNeg hbPos hcenters.1 hcenters.2

theorem Complex.logarithmicPhaseBProcessLeftClipped_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b) :
    Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower t a ≤ -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper t a := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessLeftClippedModes_iff
      t a b m).mp hm
  have hmNeg : m < 0 :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hclass.1
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hupper :
      Complex.logarithmicPhaseFourierStationaryPoint t m <
        Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t a :=
    Complex.logarithmicPhaseBProcessLeftClipped_center_lt_upper
      t ht hclass.2.2.2
  exact
    Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds_strict_right
      t ht hmNeg haPos hclass.2.1 hupper

theorem Complex.logarithmicPhaseBProcessRightClipped_lower_pos
    (t : ℝ) {b : ℤ} (hb : 1 ≤ b) :
    0 < Complex.logarithmicPhaseBProcessRightClippedCenterLower t b := by
  unfold Complex.logarithmicPhaseBProcessRightClippedCenterLower
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  exact div_pos
    (mul_pos hbPos (Complex.logarithmicPhaseBProcessScale_pos t))
    (Complex.logarithmicPhaseBProcessScale_add_one_pos t)

theorem Complex.logarithmicPhaseBProcessRightClipped_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (hb : 1 ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b) :
    Complex.logarithmicPhaseBProcessRightClippedFrequencyLower t b ≤ -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper t b := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessRightClippedModes_iff
      t a b m).mp hm
  have hmNeg : m < 0 :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hclass.1
  have hlowerPos :
      0 < Complex.logarithmicPhaseBProcessRightClippedCenterLower t b :=
    Complex.logarithmicPhaseBProcessRightClipped_lower_pos t hb
  have hlower :
      Complex.logarithmicPhaseBProcessRightClippedCenterLower t b <
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    Complex.logarithmicPhaseBProcessRightClipped_lower_lt_center
      t hclass.2.2.2
  exact
    Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds_strict_left
      t ht hmNeg hlowerPos hlower hclass.2.2.1

theorem Complex.logarithmicPhaseBProcessLeftOutside_modeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b) :
    -Complex.logarithmicPhaseBProcessLeftOutsideFrequencyUpper t a ≤ (m : ℝ) ∧
      (m : ℝ) ≤
        -Complex.logarithmicPhaseBProcessLeftOutsideFrequencyLower t a := by
  exact
    (Int.neg_cast_mem_interval_iff_cast_mem_reflected_interval).mp
      (Complex.logarithmicPhaseBProcessLeftOutside_negModeCast_bounds
        t ht a b ha hm)

theorem Complex.logarithmicPhaseBProcessRightOutside_modeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (hb : 1 ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b) :
    -Complex.logarithmicPhaseBProcessRightOutsideFrequencyUpper t b ≤ (m : ℝ) ∧
      (m : ℝ) ≤
        -Complex.logarithmicPhaseBProcessRightOutsideFrequencyLower t b := by
  exact
    (Int.neg_cast_mem_interval_iff_cast_mem_reflected_interval).mp
      (Complex.logarithmicPhaseBProcessRightOutside_negModeCast_bounds
        t ht a b hb hm)

theorem Complex.logarithmicPhaseBProcessLeftClipped_modeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b) :
    -Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper t a ≤ (m : ℝ) ∧
      (m : ℝ) ≤
        -Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower t a := by
  exact
    (Int.neg_cast_mem_interval_iff_cast_mem_reflected_interval).mp
      (Complex.logarithmicPhaseBProcessLeftClipped_negModeCast_bounds
        t ht a b ha hm)

theorem Complex.logarithmicPhaseBProcessRightClipped_modeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (hb : 1 ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b) :
    -Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper t b ≤ (m : ℝ) ∧
      (m : ℝ) ≤
        -Complex.logarithmicPhaseBProcessRightClippedFrequencyLower t b := by
  exact
    (Int.neg_cast_mem_interval_iff_cast_mem_reflected_interval).mp
      (Complex.logarithmicPhaseBProcessRightClipped_negModeCast_bounds
        t ht a b hb hm)

end

end LFunctions
end Boundary
