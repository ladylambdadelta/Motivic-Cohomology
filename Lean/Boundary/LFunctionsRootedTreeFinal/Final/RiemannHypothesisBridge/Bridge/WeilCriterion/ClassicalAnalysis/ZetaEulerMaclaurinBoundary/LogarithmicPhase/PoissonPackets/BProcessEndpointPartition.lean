import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessActiveBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeEndpointPackets

/-!
# Partition of balanced B-process endpoint modes

The active family not covered by a full balanced window is not analytically
uniform.  This owner partitions it according to the location of the stationary
center and the side on which the raw balanced window crosses the principal
block.  Centers outside `[a,b]` are nonstationary on the whole principal
interval; centers inside `[a,b]` have a one-sided clipped stationary window.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePoissonBProcessLeftOutsideModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonBProcessEndpointModes t a b).filter
    (fun m : ℤ =>
      Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ))

def Complex.logarithmicPhasePoissonBProcessRightOutsideModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonBProcessEndpointModes t a b).filter
    (fun m : ℤ =>
      (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m)

def Complex.logarithmicPhasePoissonBProcessLeftClippedModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonBProcessEndpointModes t a b).filter
    (fun m : ℤ =>
      (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m ∧
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) ∧
      Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ))

def Complex.logarithmicPhasePoissonBProcessRightClippedModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonBProcessEndpointModes t a b).filter
    (fun m : ℤ =>
      (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m ∧
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) ∧
      (b : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m)

theorem Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) := by
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ∧
        (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m := by
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhasePoissonBProcessLeftClippedModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ∧
        (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) ∧
        Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ) := by
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhasePoissonBProcessRightClippedModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ∧
        (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) ∧
        (b : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m := by
  exact Finset.mem_filter

theorem Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_active
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    m ∈ Complex.logarithmicPhasePoissonActiveModes t a b := by
  unfold Complex.logarithmicPhasePoissonBProcessEndpointModes at hm
  exact (Finset.mem_sdiff.mp hm).1

theorem Complex.logarithmicPhasePoissonBProcessEndpointMode_not_mem_interior
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    m ∉ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b := by
  unfold Complex.logarithmicPhasePoissonBProcessEndpointModes at hm
  exact (Finset.mem_sdiff.mp hm).2

theorem Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    m < 0 := by
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_active
      t a b hm
  exact
    ((Complex.mem_logarithmicPhasePoissonActiveModes_iff
      t a b m).mp hactive).2.1

theorem Complex.logarithmicPhasePoissonBProcessEndpointMode_in_modeRange
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    m ∈ Complex.logarithmicPhasePoissonModeRange t a := by
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_active
      t a b hm
  exact
    ((Complex.mem_logarithmicPhasePoissonActiveModes_iff
      t a b m).mp hactive).1

theorem Complex.logarithmicPhasePoissonBProcessEndpointMode_inside_center_has_clipped_side
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b)
    (hleftCenter :
      (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hcenterRight :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ)) :
    Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ) ∨
      (b : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m := by
  have hnotInterior :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_not_mem_interior
      t a b hm
  have hmodeRange :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_in_modeRange
      t a b hm
  have hnegative :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hm
  by_contra hnot
  have hnotLeft :
      ¬ Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ) :=
    fun h => hnot (Or.inl h)
  have hnotRight :
      ¬ (b : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m :=
    fun h => hnot (Or.inr h)
  have hleftWindow :
      (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m :=
    le_of_not_gt hnotLeft
  have hrightWindow :
      Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) :=
    le_of_not_gt hnotRight
  have hinterior :
      m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mpr
      (And.intro hmodeRange
        (And.intro hnegative
          (And.intro hleftWindow hrightWindow)))
  exact hnotInterior hinterior

theorem Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_partition
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b ∨
      m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b ∨
      m ∈ Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b ∨
      m ∈ Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b := by
  let center := Complex.logarithmicPhaseFourierStationaryPoint t m
  match lt_or_ge center (a : ℝ) with
  | Or.inl hleft =>
      exact Or.inl
        ((Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
          t a b m).mpr (And.intro hm hleft))
  | Or.inr hleft =>
      match lt_or_ge (b : ℝ) center with
      | Or.inl hright =>
          exact Or.inr (Or.inl
            ((Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
              t a b m).mpr (And.intro hm hright)))
      | Or.inr hright =>
          have hclipped :=
            Complex.logarithmicPhasePoissonBProcessEndpointMode_inside_center_has_clipped_side
              t a b hm hleft hright
          match hclipped with
          | Or.inl hleftClip =>
              exact Or.inr (Or.inr (Or.inl
                ((Complex.mem_logarithmicPhasePoissonBProcessLeftClippedModes_iff
                  t a b m).mpr
                  (And.intro hm
                    (And.intro hleft
                      (And.intro hright hleftClip))))))
          | Or.inr hrightClip =>
              exact Or.inr (Or.inr (Or.inr
                ((Complex.mem_logarithmicPhasePoissonBProcessRightClippedModes_iff
                  t a b m).mpr
                  (And.intro hm
                    (And.intro hleft
                      (And.intro hright hrightClip))))))

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_partitionUnion
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ⊆
      Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b ∪
      Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b ∪
      Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b ∪
      Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b := by
  intro m hm
  have hpartition :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_partition
      t a b hm
  match hpartition with
  | Or.inl hleftOutside =>
      exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_left _ hleftOutside))
  | Or.inr (Or.inl hrightOutside) =>
      exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_right _ hrightOutside))
  | Or.inr (Or.inr (Or.inl hleftClipped)) =>
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ hleftClipped)
  | Or.inr (Or.inr (Or.inr hrightClipped)) =>
      exact Finset.mem_union_right _ hrightClipped

end

end LFunctions
end Boundary
