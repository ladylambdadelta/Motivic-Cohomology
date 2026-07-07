import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_08

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-!
## Part20 09: YRawHoleSubspans
-/

/-- The raw-hole vertical subspan predicate is decidable because it is a conjunction of
real coordinate inequalities. -/
instance explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_decidable
    {T : ℝ}
    (ρ : ℝ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (a : ℂ) :
    Decidable
      (explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a) :=
  show
    Decidable
      ((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im ≤ ypair.y₀ ∧
        ypair.y₁ ≤ (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
  from inferInstance

/-- The shifted vertical endpoint coordinates in the raw-hole block lie between the
raw lower and upper vertical coordinates. -/
theorem explicitFormulaRectangleRawHoleYShiftedEndpointCoordinates_subspan
    {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a)) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im ≤
        explicitFormulaRectangleSortedYEndpointAt T ρ
          (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1) ∧
      explicitFormulaRectangleSortedYEndpointAt T ρ
          (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1)) ≤
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im := by
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleYUpperIndex T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  let ylo : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
  let yhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  have hylo_mem : ylo ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleBottom T ρ ha
  have hyhi_mem : yhi ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleTop T ρ ha
  have hlo_lt_len : lo < ys.length :=
    List.indexOf_lt_length.mpr hylo_mem
  have hhi_lt_len : hi < ys.length :=
    List.indexOf_lt_length.mpr hyhi_mem
  have hlo_add_i_le_hi : lo + i.1 ≤ hi := by
    calc
      lo + i.1 ≤ lo + span := by
        exact Nat.add_le_add_left (Nat.le_of_lt i.2) lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleYLowerIndex_add_spanLength T hρ ha
  have hlo_add_succ_le_hi : lo + (i.1 + 1) ≤ hi := by
    calc
      lo + (i.1 + 1) ≤ lo + span := by
        exact Nat.add_le_add_left (Nat.succ_le_of_lt i.2) lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleYLowerIndex_add_spanLength T hρ ha
  have hlo_add_i_lt_len : lo + i.1 < ys.length :=
    lt_of_le_of_lt hlo_add_i_le_hi hhi_lt_len
  have hlo_add_succ_lt_len : lo + (i.1 + 1) < ys.length :=
    lt_of_le_of_lt hlo_add_succ_le_hi hhi_lt_len
  have hleft : ylo ≤ explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1) := by
    let ilo : Fin ys.length := ⟨lo, hlo_lt_len⟩
    let ik : Fin ys.length := ⟨lo + i.1, hlo_add_i_lt_len⟩
    have hlo_le_lo_add : lo ≤ lo + i.1 :=
      Nat.le_add_right lo i.1
    calc
      ylo = explicitFormulaRectangleSortedYEndpointAt T ρ lo := by
        exact (explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex T ρ ha).symm
      _ = ys.get ilo := by
        exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hlo_lt_len
      _ ≤ ys.get ik := by
        exact (explicitFormulaRectangleSortedYEndpoints_sorted_le T ρ).rel_get_of_le
          hlo_le_lo_add
      _ = explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1) := by
        exact (explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hlo_add_i_lt_len).symm
  have hright :
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1)) ≤ yhi := by
    let ik : Fin ys.length := ⟨lo + (i.1 + 1), hlo_add_succ_lt_len⟩
    let ihi : Fin ys.length := ⟨hi, hhi_lt_len⟩
    calc
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1)) =
          ys.get ik := by
        exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hlo_add_succ_lt_len
      _ ≤ ys.get ihi := by
        exact (explicitFormulaRectangleSortedYEndpoints_sorted_le T ρ).rel_get_of_le
          hlo_add_succ_le_hi
      _ = explicitFormulaRectangleSortedYEndpointAt T ρ hi := by
        exact (explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hhi_lt_len).symm
      _ = yhi := by
        exact explicitFormulaRectangleSortedYEndpointAt_rawHoleUpperIndex T ρ ha
  exact And.intro hleft hright

/-- A vertical adjacent-pair whose coordinates are a shifted raw-hole block interval is
contained in that raw square side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_of_shiftedCoordinates
    {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (hy₀ :
      ypair.y₀ =
        explicitFormulaRectangleSortedYEndpointAt T ρ
          (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1))
    (hy₁ :
      ypair.y₁ =
        explicitFormulaRectangleSortedYEndpointAt T ρ
          (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))) :
    explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a := by
  have hcoords :
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im ≤
          explicitFormulaRectangleSortedYEndpointAt T ρ
            (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1) ∧
        explicitFormulaRectangleSortedYEndpointAt T ρ
            (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1)) ≤
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im :=
    explicitFormulaRectangleRawHoleYShiftedEndpointCoordinates_subspan hρ ha i
  exact And.intro
    (by
      calc
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im ≤
            explicitFormulaRectangleSortedYEndpointAt T ρ
              (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1) := by
          exact hcoords.1
        _ = ypair.y₀ := by
          exact hy₀.symm)
    (by
      calc
        ypair.y₁ =
            explicitFormulaRectangleSortedYEndpointAt T ρ
              (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1)) := by
          exact hy₁
        _ ≤ (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im := by
          exact hcoords.2)

/-- The vertical adjacent pair generated at a shifted raw-hole index is contained in
that raw square side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_shifted
    {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a)) :
    explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ
      (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ
        ⟨explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1,
          explicitFormulaRectangleRawHoleYLowerIndex_add_lt_sortedLength_sub_one T hρ ha i⟩)
      a := by
  let j : Fin ((explicitFormulaRectangleSortedYEndpoints T ρ).length - 1) :=
    ⟨explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1,
      explicitFormulaRectangleRawHoleYLowerIndex_add_lt_sortedLength_sub_one T hρ ha i⟩
  exact
    explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_of_shiftedCoordinates
      hρ ha i (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j)
      (explicitFormulaRectangleYAdjacentEndpointPairAt_y₀ T ρ j)
      (by
        calc
          (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j).y₁ =
              explicitFormulaRectangleSortedYEndpointAt T ρ (j.1 + 1) := by
            exact explicitFormulaRectangleYAdjacentEndpointPairAt_y₁ T ρ j
          _ =
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1)) := by
            exact congrArg
              (fun k : ℕ => explicitFormulaRectangleSortedYEndpointAt T ρ k)
              (Nat.add_assoc (explicitFormulaRectangleRawHoleYLowerIndex T ρ a) i.1 1))

/-- A generated vertical adjacent pair contained in a raw-hole side starts no earlier
than that raw-hole lower vertical endpoint index. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_lowerIndex_le
    {T ρ : ℝ} {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedYEndpoints T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j) a) :
    explicitFormulaRectangleRawHoleYLowerIndex T ρ a ≤ j.1 := by
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  let ylo : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
  have hylo_mem : ylo ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleBottom T ρ ha
  have hlo_lt_len : lo < ys.length :=
    List.indexOf_lt_length.mpr hylo_mem
  have hj_lt_len : j.1 < ys.length :=
    lt_trans (Nat.lt_succ_self j.1)
      ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := ys.length)).mp j.2)
  exact
    le_of_not_gt
      (fun hj_lt_lo : j.1 < lo =>
        let hlt : (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j).y₀ < ylo := by
          calc
            (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j).y₀ =
                explicitFormulaRectangleSortedYEndpointAt T ρ j.1 := by
              exact explicitFormulaRectangleYAdjacentEndpointPairAt_y₀ T ρ j
            _ = ys.get ⟨j.1, hj_lt_len⟩ := by
              exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hj_lt_len
            _ < ys.get ⟨lo, hlo_lt_len⟩ := by
              exact (explicitFormulaRectangleSortedYEndpoints_sorted_lt T ρ).rel_get_of_lt
                hj_lt_lo
            _ = explicitFormulaRectangleSortedYEndpointAt T ρ lo := by
              exact (explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hlo_lt_len).symm
            _ = ylo := by
              exact explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex T ρ ha
        (not_lt_of_ge hspan.1) hlt)

/-- A generated vertical adjacent pair contained in a raw-hole side ends no later than
that raw-hole upper vertical endpoint index. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_succ_le_upperIndex
    {T ρ : ℝ} {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedYEndpoints T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j) a) :
    j.1 + 1 ≤ explicitFormulaRectangleRawHoleYUpperIndex T ρ a := by
  let hi : ℕ := explicitFormulaRectangleRawHoleYUpperIndex T ρ a
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  let yhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  have hyhi_mem : yhi ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleTop T ρ ha
  have hhi_lt_len : hi < ys.length :=
    List.indexOf_lt_length.mpr hyhi_mem
  have hj_succ_lt_len : j.1 + 1 < ys.length :=
    ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := ys.length)).mp j.2)
  exact
    le_of_not_gt
      (fun hhi_lt_succ : hi < j.1 + 1 =>
        let hlt : yhi < (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j).y₁ := by
          calc
            yhi = explicitFormulaRectangleSortedYEndpointAt T ρ hi := by
              exact (explicitFormulaRectangleSortedYEndpointAt_rawHoleUpperIndex T ρ ha).symm
            _ = ys.get ⟨hi, hhi_lt_len⟩ := by
              exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hhi_lt_len
            _ < ys.get ⟨j.1 + 1, hj_succ_lt_len⟩ := by
              exact (explicitFormulaRectangleSortedYEndpoints_sorted_lt T ρ).rel_get_of_lt
                hhi_lt_succ
            _ = explicitFormulaRectangleSortedYEndpointAt T ρ (j.1 + 1) := by
              exact (explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hj_succ_lt_len).symm
            _ = (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j).y₁ := by
              exact (explicitFormulaRectangleYAdjacentEndpointPairAt_y₁ T ρ j).symm
        (not_lt_of_ge hspan.2) hlt)

/-- A generated vertical adjacent-pair subspan contained in a raw-hole side has a unique
offset inside the raw-hole span. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_offset_lt_span
    {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedYEndpoints T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j) a) :
    j.1 - explicitFormulaRectangleRawHoleYLowerIndex T ρ a <
      explicitFormulaRectangleRawHoleYSpanLength T ρ a := by
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleYUpperIndex T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  have hlo_le_j : lo ≤ j.1 :=
    explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_lowerIndex_le
      ha j hspan
  have hsucc_le_hi : j.1 + 1 ≤ hi :=
    explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_succ_le_upperIndex
      ha j hspan
  have hj_lt_hi : j.1 < hi :=
    Nat.lt_of_succ_le hsucc_le_hi
  have hj_lt_lo_add_span : j.1 < lo + span := by
    calc
      j.1 < hi := by
        exact hj_lt_hi
      _ = lo + span := by
        exact (explicitFormulaRectangleRawHoleYLowerIndex_add_spanLength T hρ ha).symm
  exact
    (Nat.sub_lt_iff_lt_add hlo_le_j).mpr hj_lt_lo_add_span

/-- The offset recovered from a contained generated vertical adjacent-pair subspan
reconstructs its source index. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_lower_add_offset
    {T ρ : ℝ} {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedYEndpoints T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleYAdjacentEndpointPairAt T ρ j) a) :
    explicitFormulaRectangleRawHoleYLowerIndex T ρ a +
        (j.1 - explicitFormulaRectangleRawHoleYLowerIndex T ρ a) =
      j.1 := by
  exact
    Nat.add_sub_of_le
      (explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_lowerIndex_le
        ha j hspan)

/-- Raw square-hole vertical contribution carried by one sorted vertical slice. -/
noncomputable def explicitFormulaRectangleVerticalHoleSliceContribution
    (f : ZetaAdmissibleFunction) (T ρ : ℝ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) : ℂ :=
  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
    if _hspan :
        explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    else
      0

/-- The right raw-hole vertical slice sum can be grouped first by raw singular
coordinate. -/
theorem explicitFormulaRectangleVerticalHoleRightSliceContributionSum_groupedByRawCoordinate
    (f : ZetaAdmissibleFunction) (T ρ : ℝ) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
  exact
    explicitFormulaRectangleListSum_finset_sum
      (explicitFormulaRectangleRawSingularCoordinates T)
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        fun a : ℂ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)

/-- The left raw-hole vertical slice sum can be grouped first by raw singular
coordinate. -/
theorem explicitFormulaRectangleVerticalHoleLeftSliceContributionSum_groupedByRawCoordinate
    (f : ZetaAdmissibleFunction) (T ρ : ℝ) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
  exact
    explicitFormulaRectangleListSum_finset_sum
      (explicitFormulaRectangleRawSingularCoordinates T)
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        fun a : ℂ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)

/-- The sorted vertical adjacent-pair filter for one raw-hole side is exactly the shifted
subrange between the raw lower and upper vertical endpoint indices. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
    {T ρ : ℝ} {a : ℂ}
    (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (G : ExplicitFormulaRectangleVerticalEndpointDataEdge → ℂ) (x : ℝ) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            G ((ypair.y₀, ypair.y₁), x)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
          G
            ((explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1),
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))), x))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) := by
  let n : ℕ := (explicitFormulaRectangleSortedYEndpoints T ρ).length - 1
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let pairAt : Fin n → ExplicitFormulaRectangleYAdjacentEndpointPair T ρ :=
    explicitFormulaRectangleYAdjacentEndpointPairAt T ρ
  let P : Fin n → Prop :=
    fun j => explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ (pairAt j) a
  let g : Fin n → ℂ :=
    fun j => G (((pairAt j).y₀, (pairAt j).y₁), x)
  let gShift : Fin span → ℂ :=
    fun i =>
      G
        ((explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1),
          explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1))), x)
  have hleft :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              G ((ypair.y₀, ypair.y₁), x)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        ∑ j : Fin n, if _h : P j then g j else 0 := by
    exact
      explicitFormulaRectangleListSum_YAdjacentEndpointPairsFromSortedEndpoints_eq_indexSum
        (g :=
          fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              G ((ypair.y₀, ypair.y₁), x)
            else
              0)
  have hblock :
      (∑ j : Fin n, if _h : P j then g j else 0) =
        ∑ i : Fin span, gShift i := by
    exact
      explicitFormulaRectangleFinSum_contiguousBlock_ite_eq_shifted
        lo P g gShift
        (explicitFormulaRectangleRawHoleYLowerIndex_add_lt_sortedLength_sub_one
          T hρ ha)
        (fun i =>
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_shifted
            hρ ha i)
        (fun j hspan =>
          And.intro
            (explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_offset_lt_span
              hρ ha j hspan)
            (explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole_pairAt_lower_add_offset
              ha j hspan))
        (fun i => by
          let j : Fin n :=
            ⟨lo + i.1,
              explicitFormulaRectangleRawHoleYLowerIndex_add_lt_sortedLength_sub_one
                T hρ ha i⟩
          have hy₀ :
              (pairAt j).y₀ =
                explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1) :=
            explicitFormulaRectangleYAdjacentEndpointPairAt_y₀ T ρ j
          have hy₁_base :
              (pairAt j).y₁ =
                explicitFormulaRectangleSortedYEndpointAt T ρ ((lo + i.1) + 1) :=
            explicitFormulaRectangleYAdjacentEndpointPairAt_y₁ T ρ j
          have hy₁_index :
              explicitFormulaRectangleSortedYEndpointAt T ρ ((lo + i.1) + 1) =
                explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1)) :=
            congrArg
              (fun k : ℕ => explicitFormulaRectangleSortedYEndpointAt T ρ k)
              (Nat.add_assoc lo i.1 1)
          have hy₁ :
              (pairAt j).y₁ =
                explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1)) :=
            Eq.trans hy₁_base hy₁_index
          have hpair :
              (((pairAt j).y₀, (pairAt j).y₁), x) =
                ((explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1),
                  explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1))), x) :=
            congrArg
              (fun p : ℝ × ℝ => (p, x))
              (Prod.ext hy₀ hy₁)
          exact congrArg G hpair)
  have hright :
      explicitFormulaRectangleListSum
          (fun i : Fin span => gShift i)
          (List.ofFn (fun i : Fin span => i)) =
        ∑ i : Fin span, gShift i := by
    exact
      explicitFormulaRectangleListSum_ofFn
        (fun i : Fin span => i)
        (fun i : Fin span => gShift i)
  exact Eq.trans (Eq.trans hleft hblock) hright.symm

/-- A vertical raw-hole block telescopes a fixed horizontal-span bottom-minus-top
coordinate scan from the raw bottom side to the raw top side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_horizontalScanSub_eq_rawSides
    (f : ZetaAdmissibleFunction)
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  let edge : ℕ → ℂ :=
    fun k =>
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((xpair.x₀, xpair.x₁), explicitFormulaRectangleSortedYEndpointAt T ρ k)
  have hfilter :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁), ypair.y₀) -
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁), ypair.y₁)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁),
                  explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1)) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁),
                  explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1))))
          (List.ofFn (fun i : Fin span => i)) := by
    exact
      explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
        hρ ha
        (fun edge : ExplicitFormulaRectangleVerticalEndpointDataEdge =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), edge.1.1) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), edge.1.2))
        xpair.x₀
  have hcommon :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁),
                  explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1)) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁),
                  explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1))))
          (List.ofFn (fun i : Fin span => i)) =
        explicitFormulaRectangleListSum
          (fun i : Fin span => edge (lo + i.1) - edge (lo + (i.1 + 1)))
          (List.ofFn (fun i : Fin span => i)) := by
    exact congrArg
      (fun g : Fin span → ℂ =>
        explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin span => i)))
      (funext
        (fun i =>
          congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁),
                    explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1)) - z)
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral_eq_top_sameCoordinate
              f xpair.x₀ xpair.x₁
              (explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1))))))
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin span => edge (lo + i.1) - edge (lo + (i.1 + 1)))
          (List.ofFn (fun i : Fin span => i)) =
        edge lo - edge (lo + span) :=
    explicitFormulaRectangleListSum_ofFn_consecutiveBackwardDifferences_shift edge lo
  have hlo :
      explicitFormulaRectangleSortedYEndpointAt T ρ lo =
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im :=
    explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex T ρ ha
  have hhi :
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span) =
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im :=
    explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex_add_spanLength T hρ ha
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁),
                  explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1)) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁),
                  explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1))))
          (List.ofFn (fun i : Fin span => i)) := by
      exact hfilter
    _ =
        explicitFormulaRectangleListSum
          (fun i : Fin span => edge (lo + i.1) - edge (lo + (i.1 + 1)))
          (List.ofFn (fun i : Fin span => i)) := by
      exact hcommon
    _ = edge lo - edge (lo + span) := by
      exact htelescope
    _ =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
      exact congrArg₂ HSub.hSub
        (congrArg
          (fun y : ℝ =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), y))
          hlo)
        (congrArg
          (fun y : ℝ =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), y))
          hhi)
    _ =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) - z)
        (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral_eq_top_sameCoordinate
          f xpair.x₀ xpair.x₁
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)

/-- Right raw-hole vertical side telescope after the finite subspan classification has
selected exactly the sorted adjacent intervals contained in that raw square side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_rightIntegralSum_eq_coordinate_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im),
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) := by
  let x : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re
  have hfilter :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁), x)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1),
                explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))), x))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) :=
    explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
      hρ ha (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f) x
  have hsubrange :
      explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1),
                explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))), x))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im), x) :=
    explicitFormulaRectangleRawHoleYSubrangeVerticalIntegralSum_eq_coordinate
      f T hρ ha x hint
  exact Eq.trans hfilter hsubrange

/-- Right raw-hole vertical side telescope expressed in the raw endpoint-data box
normalization. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_rightIntegralSum_eq_rawBoxRight_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleBoxRightEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) := by
      exact
        explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_rightIntegralSum_eq_coordinate_of_integrable
          f F hT_nonneg hρ hclosed ha hint
    _ =
        explicitFormulaRectangleBoxRightEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_rightEdgeIntegral_eq_coordinate
          f ρ a).symm

/-- Left raw-hole vertical side telescope after the finite subspan classification has
selected exactly the sorted adjacent intervals contained in that raw square side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_leftIntegralSum_eq_coordinate_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im),
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
  let x : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re
  have hfilter :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁), x)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1),
                explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))), x))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) :=
    explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
      hρ ha (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f) x
  have hsubrange :
      explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1),
                explicitFormulaRectangleSortedYEndpointAt T ρ
                  (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))), x))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im), x) :=
    explicitFormulaRectangleRawHoleYSubrangeLeftVerticalIntegralSum_eq_coordinate
      f T hρ ha x hint
  exact Eq.trans hfilter hsubrange

/-- Left raw-hole vertical side telescope expressed in the raw endpoint-data box
normalization. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_leftIntegralSum_eq_rawBoxLeft_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleBoxLeftEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
      exact
        explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_leftIntegralSum_eq_coordinate_of_integrable
          f F hT_nonneg hρ hclosed ha hint
    _ =
        explicitFormulaRectangleBoxLeftEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_leftEdgeIntegral_eq_coordinate
          f ρ a).symm

/-- The sorted vertical subdivision subspans contained in a raw square side assemble to
the two full vertical sides of that raw square. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_verticalIntegralSums_eq_rawBoxSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) →
    (explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) →
    (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleBoxRightEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a)) ∧
    (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleBoxLeftEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a)) := by
  intro hright hleft
  exact
    And.intro
      (explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_rightIntegralSum_eq_rawBoxRight_of_integrable
        f F hT_nonneg hρ hclosed ha hright)
      (explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_leftIntegralSum_eq_rawBoxLeft_of_integrable
        f F hT_nonneg hρ hclosed ha hleft)

/-- The sorted vertical subdivision subspans contained in a raw square side assemble to
that raw square's full right side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_rightIntegralSum_eq_rawBoxRight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleBoxRightEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  exact
    explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_rightIntegralSum_eq_rawBoxRight_of_integrable
      f F hT_nonneg hρ hclosed ha hint

/-- The sorted vertical subdivision subspans contained in a raw square side assemble to
that raw square's full left side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_leftIntegralSum_eq_rawBoxLeft
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleBoxLeftEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  exact
    explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_leftIntegralSum_eq_rawBoxLeft_of_integrable
      f F hT_nonneg hρ hclosed ha hint

/- The sorted vertical subdivision assembles to a full right vertical endpoint-data edge
once interval-integrability on the sorted adjacent subintervals is supplied. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
