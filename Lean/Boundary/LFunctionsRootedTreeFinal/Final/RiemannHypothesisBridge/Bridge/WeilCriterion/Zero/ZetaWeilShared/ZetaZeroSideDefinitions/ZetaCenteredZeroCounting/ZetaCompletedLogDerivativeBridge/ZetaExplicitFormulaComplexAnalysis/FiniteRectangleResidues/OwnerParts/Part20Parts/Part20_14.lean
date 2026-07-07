import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_13

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
## Part20 14: XRawHoleSubspans
-/

/-- The raw-hole horizontal subspan predicate is decidable because it is a conjunction
of real coordinate inequalities. -/
instance explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_decidable_part20_14
    {F : ExplicitFormulaContourFamily} {T : ℝ}
    (ρ : ℝ)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (a : ℂ) :
    Decidable
      (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a) :=
  show
    Decidable
      ((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re ≤ xpair.x₀ ∧
        xpair.x₁ ≤ (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
  from inferInstance

/-- The shifted horizontal endpoint coordinates in the raw-hole block lie between the
raw left and right horizontal coordinates. -/
theorem explicitFormulaRectangleRawHoleXShiftedEndpointCoordinates_subspan
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re ≤
        explicitFormulaRectangleSortedXEndpointAt F T ρ
          (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1) ∧
      explicitFormulaRectangleSortedXEndpointAt F T ρ
          (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1)) ≤
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re := by
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleXUpperIndex F T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  let xlo : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re
  let xhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re
  have hxlo_mem : xlo ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleLeft F T ρ ha
  have hxhi_mem : xhi ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleRight F T ρ ha
  have hlo_lt_len : lo < xs.length :=
    List.indexOf_lt_length.mpr hxlo_mem
  have hhi_lt_len : hi < xs.length :=
    List.indexOf_lt_length.mpr hxhi_mem
  have hlo_add_i_le_hi : lo + i.1 ≤ hi := by
    calc
      lo + i.1 ≤ lo + span := by
        exact Nat.add_le_add_left (Nat.le_of_lt i.2) lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleXLowerIndex_add_spanLength F T hρ ha
  have hlo_add_succ_le_hi : lo + (i.1 + 1) ≤ hi := by
    calc
      lo + (i.1 + 1) ≤ lo + span := by
        exact Nat.add_le_add_left (Nat.succ_le_of_lt i.2) lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleXLowerIndex_add_spanLength F T hρ ha
  have hlo_add_i_lt_len : lo + i.1 < xs.length :=
    lt_of_le_of_lt hlo_add_i_le_hi hhi_lt_len
  have hlo_add_succ_lt_len : lo + (i.1 + 1) < xs.length :=
    lt_of_le_of_lt hlo_add_succ_le_hi hhi_lt_len
  have hleft : xlo ≤ explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1) := by
    let ilo : Fin xs.length := ⟨lo, hlo_lt_len⟩
    let ik : Fin xs.length := ⟨lo + i.1, hlo_add_i_lt_len⟩
    have hlo_le_lo_add : lo ≤ lo + i.1 :=
      Nat.le_add_right lo i.1
    calc
      xlo = explicitFormulaRectangleSortedXEndpointAt F T ρ lo := by
        exact (explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex F T ρ ha).symm
      _ = xs.get ilo := by
        exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hlo_lt_len
      _ ≤ xs.get ik := by
        exact (explicitFormulaRectangleSortedXEndpoints_sorted_le F T ρ).rel_get_of_le
          hlo_le_lo_add
      _ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1) := by
        exact (explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hlo_add_i_lt_len).symm
  have hright :
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) ≤ xhi := by
    let ik : Fin xs.length := ⟨lo + (i.1 + 1), hlo_add_succ_lt_len⟩
    let ihi : Fin xs.length := ⟨hi, hhi_lt_len⟩
    calc
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) =
          xs.get ik := by
        exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hlo_add_succ_lt_len
      _ ≤ xs.get ihi := by
        exact (explicitFormulaRectangleSortedXEndpoints_sorted_le F T ρ).rel_get_of_le
          hlo_add_succ_le_hi
      _ = explicitFormulaRectangleSortedXEndpointAt F T ρ hi := by
        exact (explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hhi_lt_len).symm
      _ = xhi := by
        exact explicitFormulaRectangleSortedXEndpointAt_rawHoleUpperIndex F T ρ ha
  exact And.intro hleft hright

/-- A horizontal adjacent-pair whose coordinates are a shifted raw-hole block interval is
contained in that raw square side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_of_shiftedCoordinates
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a))
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (hx₀ :
      xpair.x₀ =
        explicitFormulaRectangleSortedXEndpointAt F T ρ
          (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1))
    (hx₁ :
      xpair.x₁ =
        explicitFormulaRectangleSortedXEndpointAt F T ρ
          (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))) :
    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a := by
  have hcoords :
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re ≤
          explicitFormulaRectangleSortedXEndpointAt F T ρ
            (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1) ∧
        explicitFormulaRectangleSortedXEndpointAt F T ρ
            (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1)) ≤
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re :=
    explicitFormulaRectangleRawHoleXShiftedEndpointCoordinates_subspan hρ ha i
  exact And.intro
    (by
      calc
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re ≤
            explicitFormulaRectangleSortedXEndpointAt F T ρ
              (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1) := by
          exact hcoords.1
        _ = xpair.x₀ := by
          exact hx₀.symm)
    (by
      calc
        xpair.x₁ =
            explicitFormulaRectangleSortedXEndpointAt F T ρ
              (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1)) := by
          exact hx₁
        _ ≤ (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re := by
          exact hcoords.2)

/-- The horizontal adjacent pair generated at a shifted raw-hole index is contained in
that raw square side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_shifted
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) :
    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ
      (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ
        ⟨explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1,
          explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one F T hρ ha i⟩)
      a := by
  let j : Fin ((explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1) :=
    ⟨explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1,
      explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one F T hρ ha i⟩
  exact
    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_of_shiftedCoordinates
      hρ ha i (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j)
      (explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ j)
      (by
        calc
          (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j).x₁ =
              explicitFormulaRectangleSortedXEndpointAt F T ρ (j.1 + 1) := by
            exact explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ j
          _ =
              explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1)) := by
            exact congrArg
              (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
              (Nat.add_assoc (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a) i.1 1))

/-- A generated horizontal adjacent pair contained in a raw-hole side starts no earlier
than that raw-hole left horizontal endpoint index. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_lowerIndex_le
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j) a) :
    explicitFormulaRectangleRawHoleXLowerIndex F T ρ a ≤ j.1 := by
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  let xlo : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re
  have hxlo_mem : xlo ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleLeft F T ρ ha
  have hlo_lt_len : lo < xs.length :=
    List.indexOf_lt_length.mpr hxlo_mem
  have hj_lt_len : j.1 < xs.length :=
    lt_trans (Nat.lt_succ_self j.1)
      ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := xs.length)).mp j.2)
  exact
    le_of_not_gt
      (fun hj_lt_lo : j.1 < lo =>
        let hlt : (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j).x₀ < xlo := by
          calc
            (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j).x₀ =
                explicitFormulaRectangleSortedXEndpointAt F T ρ j.1 := by
              exact explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ j
            _ = xs.get ⟨j.1, hj_lt_len⟩ := by
              exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hj_lt_len
            _ < xs.get ⟨lo, hlo_lt_len⟩ := by
              exact (explicitFormulaRectangleSortedXEndpoints_sorted_lt F T ρ).rel_get_of_lt
                hj_lt_lo
            _ = explicitFormulaRectangleSortedXEndpointAt F T ρ lo := by
              exact (explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hlo_lt_len).symm
            _ = xlo := by
              exact explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex F T ρ ha
        (not_lt_of_ge hspan.1) hlt)

/-- A generated horizontal adjacent pair contained in a raw-hole side ends no later than
that raw-hole right horizontal endpoint index. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_succ_le_upperIndex
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j) a) :
    j.1 + 1 ≤ explicitFormulaRectangleRawHoleXUpperIndex F T ρ a := by
  let hi : ℕ := explicitFormulaRectangleRawHoleXUpperIndex F T ρ a
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  let xhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re
  have hxhi_mem : xhi ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleRight F T ρ ha
  have hhi_lt_len : hi < xs.length :=
    List.indexOf_lt_length.mpr hxhi_mem
  have hj_succ_lt_len : j.1 + 1 < xs.length :=
    ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := xs.length)).mp j.2)
  exact
    le_of_not_gt
      (fun hhi_lt_succ : hi < j.1 + 1 =>
        let hlt : xhi < (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j).x₁ := by
          calc
            xhi = explicitFormulaRectangleSortedXEndpointAt F T ρ hi := by
              exact (explicitFormulaRectangleSortedXEndpointAt_rawHoleUpperIndex F T ρ ha).symm
            _ = xs.get ⟨hi, hhi_lt_len⟩ := by
              exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hhi_lt_len
            _ < xs.get ⟨j.1 + 1, hj_succ_lt_len⟩ := by
              exact (explicitFormulaRectangleSortedXEndpoints_sorted_lt F T ρ).rel_get_of_lt
                hhi_lt_succ
            _ = explicitFormulaRectangleSortedXEndpointAt F T ρ (j.1 + 1) := by
              exact (explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hj_succ_lt_len).symm
            _ = (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j).x₁ := by
              exact (explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ j).symm
        (not_lt_of_ge hspan.2) hlt)

/-- A generated horizontal adjacent-pair subspan contained in a raw-hole side has a
unique offset inside the raw-hole span. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_offset_lt_span
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ} (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j) a) :
    j.1 - explicitFormulaRectangleRawHoleXLowerIndex F T ρ a <
      explicitFormulaRectangleRawHoleXSpanLength F T ρ a := by
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleXUpperIndex F T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  have hlo_le_j : lo ≤ j.1 :=
    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_lowerIndex_le
      ha j hspan
  have hsucc_le_hi : j.1 + 1 ≤ hi :=
    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_succ_le_upperIndex
      ha j hspan
  have hj_lt_hi : j.1 < hi :=
    Nat.lt_of_succ_le hsucc_le_hi
  have hj_lt_lo_add_span : j.1 < lo + span := by
    calc
      j.1 < hi := by
        exact hj_lt_hi
      _ = lo + span := by
        exact (explicitFormulaRectangleRawHoleXLowerIndex_add_spanLength F T hρ ha).symm
  exact
    (Nat.sub_lt_iff_lt_add hlo_le_j).mpr hj_lt_lo_add_span

/-- The offset recovered from a contained generated horizontal adjacent-pair subspan
reconstructs its source index. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_lower_add_offset
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (j : Fin ((explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1))
    (hspan :
      explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ
        (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ j) a) :
    explicitFormulaRectangleRawHoleXLowerIndex F T ρ a +
        (j.1 - explicitFormulaRectangleRawHoleXLowerIndex F T ρ a) =
      j.1 := by
  exact
    Nat.add_sub_of_le
      (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_lowerIndex_le
        ha j hspan)

/-- The proof-carrying horizontal adjacent pair generated by the `i`th interval in the
raw-hole horizontal block for `a`. -/
noncomputable def explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt
    (F : ExplicitFormulaContourFamily) {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) :
    ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ :=
  explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ
    ⟨explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1,
      explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
        F T hρ ha i⟩

/-- The generated raw-hole horizontal adjacent pair carries its own subspan proof. -/
theorem explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt_subspan
    (F : ExplicitFormulaContourFamily) {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) :
    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ
      (explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt F hρ a ha i) a := by
  exact
    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_shifted
      hρ ha i

/-- Bottom edge contribution of the `i`th generated horizontal slice of the raw hole `a`. -/
noncomputable def explicitFormulaRectangleRawHoleXBlockBottomSliceContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) : ℂ :=
  let xpair := explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt F hρ a ha i
  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
    ((xpair.x₀, xpair.x₁),
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)

/-- Top edge contribution of the `i`th generated horizontal slice of the raw hole `a`. -/
noncomputable def explicitFormulaRectangleRawHoleXBlockTopSliceContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) : ℂ :=
  let xpair := explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt F hρ a ha i
  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
    ((xpair.x₀, xpair.x₁),
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)

/-- Bottom-minus-top contribution of the `i`th generated horizontal slice of the raw
hole `a`. -/
noncomputable def explicitFormulaRectangleRawHoleXBlockSliceContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) : ℂ :=
  explicitFormulaRectangleRawHoleXBlockBottomSliceContribution f F hρ a ha i -
    explicitFormulaRectangleRawHoleXBlockTopSliceContribution f F hρ a ha i

/-- Constructive bottom contribution of a raw hole, generated by its contiguous horizontal
block rather than by a decidable predicate filter. -/
noncomputable def explicitFormulaRectangleRawHoleXBlockBottomContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) : ℂ :=
  explicitFormulaRectangleListSum
    (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
      explicitFormulaRectangleRawHoleXBlockBottomSliceContribution f F hρ a ha i)
    (List.ofFn
      (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i))

/-- Constructive top contribution of a raw hole, generated by its contiguous horizontal
block rather than by a decidable predicate filter. -/
noncomputable def explicitFormulaRectangleRawHoleXBlockTopContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) : ℂ :=
  explicitFormulaRectangleListSum
    (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
      explicitFormulaRectangleRawHoleXBlockTopSliceContribution f F hρ a ha i)
    (List.ofFn
      (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i))

/-- Constructive bottom-minus-top contribution of a raw hole, generated by its contiguous
horizontal block rather than by a decidable predicate filter. -/
noncomputable def explicitFormulaRectangleRawHoleXBlockContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) : ℂ :=
  explicitFormulaRectangleListSum
    (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
      explicitFormulaRectangleRawHoleXBlockSliceContribution f F hρ a ha i)
    (List.ofFn
      (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i))

/-- Raw square-hole horizontal contribution carried by one sorted horizontal slice. -/
noncomputable def explicitFormulaRectangleHorizontalHoleSliceContribution
    (f : ZetaAdmissibleFunction) (T ρ : ℝ)
    {F : ExplicitFormulaContourFamily}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) : ℂ :=
  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
    if _hspan :
        explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    else
      0

/-- The bottom raw-hole horizontal slice sum can be grouped first by raw singular
coordinate. -/
theorem explicitFormulaRectangleHorizontalHoleBottomSliceContributionSum_groupedByRawCoordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ : ℝ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0)
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) := by
  exact
    explicitFormulaRectangleListSum_finset_sum
      (explicitFormulaRectangleRawSingularCoordinates T)
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        fun a : ℂ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0)
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)

/-- The top raw-hole horizontal slice sum can be grouped first by raw singular
coordinate. -/
theorem explicitFormulaRectangleHorizontalHoleTopSliceContributionSum_groupedByRawCoordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ : ℝ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0)
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) := by
  exact
    explicitFormulaRectangleListSum_finset_sum
      (explicitFormulaRectangleRawSingularCoordinates T)
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        fun a : ℂ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0)
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)

/-- The sorted horizontal adjacent-pair filter for one raw-hole side is exactly the
shifted subrange between the raw left and right horizontal endpoint indices. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} {a : ℂ}
    (hρ : 0 < ρ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (G : ExplicitFormulaRectangleHorizontalEndpointDataEdge → ℂ) (y : ℝ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            G ((xpair.x₀, xpair.x₁), y)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
          G
            ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
              explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))), y))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) := by
  let n : ℕ := (explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let pairAt : Fin n → ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ :=
    explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ
  let P : Fin n → Prop :=
    fun j => explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ (pairAt j) a
  let g : Fin n → ℂ :=
    fun j => G (((pairAt j).x₀, (pairAt j).x₁), y)
  let gShift : Fin span → ℂ :=
    fun i =>
      G
        ((explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1),
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))), y)
  have hleft :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              G ((xpair.x₀, xpair.x₁), y)
            else
              0)
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        ∑ j : Fin n, if _h : P j then g j else 0 := by
    exact
      explicitFormulaRectangleListSum_XAdjacentEndpointPairsFromSortedEndpoints_eq_indexSum
        (g :=
          fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              G ((xpair.x₀, xpair.x₁), y)
            else
              0)
  have hblock :
      (∑ j : Fin n, if _h : P j then g j else 0) =
        ∑ i : Fin span, gShift i := by
    exact
      explicitFormulaRectangleFinSum_contiguousBlock_ite_eq_shifted
        lo P g gShift
        (explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
          F T hρ ha)
        (fun i =>
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_shifted
            hρ ha i)
        (fun j hspan =>
          And.intro
            (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_offset_lt_span
              hρ ha j hspan)
            (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole_pairAt_lower_add_offset
              ha j hspan))
        (fun i => by
          let j : Fin n :=
            ⟨lo + i.1,
              explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                F T hρ ha i⟩
          have hx₀ :
              (pairAt j).x₀ =
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1) :=
            explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ j
          have hx₁_base :
              (pairAt j).x₁ =
                explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) :=
            explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ j
          have hx₁_index :
              explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) =
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
            congrArg
              (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
              (Nat.add_assoc lo i.1 1)
          have hx₁ :
              (pairAt j).x₁ =
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
            Eq.trans hx₁_base hx₁_index
          have hpair :
              (((pairAt j).x₀, (pairAt j).x₁), y) =
                ((explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1),
                  explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))), y) :=
            congrArg
              (fun p : ℝ × ℝ => (p, y))
              (Prod.ext hx₀ hx₁)
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

/-- A horizontal raw-hole block telescopes a fixed vertical-span right-minus-left
coordinate scan from the raw left side to the raw right side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_verticalScanSub_eq_rawSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let edge : ℕ → ℂ :=
    fun k =>
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((ypair.y₀, ypair.y₁), explicitFormulaRectangleSortedXEndpointAt F T ρ k)
  have hfilter :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                  f ((ypair.y₀, ypair.y₁), xpair.x₁) -
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                  f ((ypair.y₀, ypair.y₁), xpair.x₀)
            else
              0)
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁),
                  explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁),
                  explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1)))
          (List.ofFn (fun i : Fin span => i)) := by
    exact
      explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
        hρ ha
        (fun edge : ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), edge.1.2) -
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), edge.1.1))
        ypair.y₀
  have hcommon :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁),
                  explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁),
                  explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1)))
          (List.ofFn (fun i : Fin span => i)) =
        explicitFormulaRectangleListSum
          (fun i : Fin span => edge (lo + (i.1 + 1)) - edge (lo + i.1))
          (List.ofFn (fun i : Fin span => i)) := by
    exact congrArg
      (fun g : Fin span → ℂ =>
        explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin span => i)))
      (funext
        (fun i =>
          congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                  f ((ypair.y₀, ypair.y₁),
                    explicitFormulaRectangleSortedXEndpointAt F T ρ
                      (lo + (i.1 + 1))) - z)
            (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral_eq_left_sameCoordinate
              f ypair.y₀ ypair.y₁
              (explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1)))))
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin span => edge (lo + (i.1 + 1)) - edge (lo + i.1))
          (List.ofFn (fun i : Fin span => i)) =
        edge (lo + span) - edge lo :=
    explicitFormulaRectangleListSum_ofFn_consecutiveForwardDifferences_shift edge lo
  have hlo :
      explicitFormulaRectangleSortedXEndpointAt F T ρ lo =
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re :=
    explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex F T ρ ha
  have hhi :
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span) =
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re :=
    explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex_add_spanLength F T hρ ha
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁),
                  explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁),
                  explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1)))
          (List.ofFn (fun i : Fin span => i)) := by
      exact hfilter
    _ =
        explicitFormulaRectangleListSum
          (fun i : Fin span => edge (lo + (i.1 + 1)) - edge (lo + i.1))
          (List.ofFn (fun i : Fin span => i)) := by
      exact hcommon
    _ = edge (lo + span) - edge lo := by
      exact htelescope
    _ =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
      exact congrArg₂ HSub.hSub
        (congrArg
          (fun x : ℝ =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), x))
          hhi)
        (congrArg
          (fun x : ℝ =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), x))
          hlo)
    _ =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) - z)
        (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral_eq_left_sameCoordinate
          f ypair.y₀ ypair.y₁
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)

/-- Bottom raw-hole horizontal side telescope after the finite subspan classification has
selected exactly the sorted adjacent intervals contained in that raw square side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_bottomIntegralSum_eq_coordinate_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
  have hfilter :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), y)
            else
              0)
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))), y))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) :=
    explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
      hρ ha (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f) y
  have hsubrange :
      explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))), y))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) :=
    explicitFormulaRectangleRawHoleXSubrangeHorizontalIntegralSum_eq_coordinate
      f F T hρ ha y hint
  exact Eq.trans hfilter hsubrange

/-- A generated bottom raw-hole horizontal block is the explicit endpoint-list sum over
the generated contiguous x-subdivision. -/
theorem explicitFormulaRectangleRawHoleXBlockBottomContribution_eq_generatedEndpointListSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha =
      explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
              explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  exact congrArg
    (fun g : Fin span → ℂ =>
      explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin span => i)))
    (funext
      (fun i =>
        let xpair := explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt F hρ a ha i
        have hx₀ :
            xpair.x₀ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1) :=
          explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ
            ⟨lo + i.1,
              explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                F T hρ ha i⟩
        have hx₁_base :
            xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) :=
          explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ
            ⟨lo + i.1,
              explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                F T hρ ha i⟩
        have hx₁_index :
            explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) =
              explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
          congrArg
            (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
            (Nat.add_assoc lo i.1 1)
        have hx₁ :
            xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
          Eq.trans hx₁_base hx₁_index
        congrArg
          (fun endpoints : ℝ × ℝ =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f (endpoints, y))
          (Prod.ext hx₀ hx₁)))

/-- A generated top raw-hole horizontal block is the explicit endpoint-list sum over
the generated contiguous x-subdivision. -/
theorem explicitFormulaRectangleRawHoleXBlockTopContribution_eq_generatedEndpointListSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha =
      explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
              explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  exact congrArg
    (fun g : Fin span → ℂ =>
      explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin span => i)))
    (funext
      (fun i =>
        let xpair := explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt F hρ a ha i
        have hx₀ :
            xpair.x₀ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1) :=
          explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ
            ⟨lo + i.1,
              explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                F T hρ ha i⟩
        have hx₁_base :
            xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) :=
          explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ
            ⟨lo + i.1,
              explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                F T hρ ha i⟩
        have hx₁_index :
            explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) =
              explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
          congrArg
            (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
            (Nat.add_assoc lo i.1 1)
        have hx₁ :
            xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
          Eq.trans hx₁_base hx₁_index
        congrArg
          (fun endpoints : ℝ × ℝ =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f (endpoints, y))
          (Prod.ext hx₀ hx₁)))

/-- Constructive bottom raw-hole horizontal side telescope over the generated raw-hole
block, with no predicate-filtered adjacent-pair sum. -/
theorem explicitFormulaRectangleRawHoleXBlockBottomContribution_eq_coordinate_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) :
    explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  have hgenerated :
      explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha =
        explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))), y))
          (List.ofFn (fun i : Fin span => i)) := by
    exact congrArg
      (fun g : Fin span → ℂ =>
        explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin span => i)))
      (funext
        (fun i =>
          let xpair := explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt F hρ a ha i
          have hx₀ :
              xpair.x₀ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1) :=
            explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ
              ⟨lo + i.1,
                explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                  F T hρ ha i⟩
          have hx₁_base :
              xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) :=
            explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ
              ⟨lo + i.1,
                explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                  F T hρ ha i⟩
          have hx₁_index :
              explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) =
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
            congrArg
              (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
              (Nat.add_assoc lo i.1 1)
          have hx₁ :
              xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
            Eq.trans hx₁_base hx₁_index
          congrArg
            (fun endpoints : ℝ × ℝ =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f (endpoints, y))
            (Prod.ext hx₀ hx₁)))
  have hsubrange :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))), y))
          (List.ofFn (fun i : Fin span => i)) =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) :=
    explicitFormulaRectangleRawHoleXSubrangeHorizontalIntegralSum_eq_coordinate
      f F T hρ ha y hint
  exact Eq.trans hgenerated hsubrange

/-- Constructive bottom raw-hole horizontal side telescope in raw endpoint-data box
normalization. -/
theorem explicitFormulaRectangleRawHoleXBlockBottomContribution_eq_rawBoxBottom_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) :
    explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha =
      explicitFormulaRectangleBoxBottomEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  calc
    explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) := by
      exact
        explicitFormulaRectangleRawHoleXBlockBottomContribution_eq_coordinate_of_integrable
          f F hρ ha hint
    _ =
        explicitFormulaRectangleBoxBottomEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_bottomEdgeIntegral_eq_coordinate
          f ρ a).symm

/-- Bottom raw-hole horizontal side telescope expressed in the raw endpoint-data box
normalization. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_bottomIntegralSum_eq_rawBoxBottom_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBoxBottomEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) := by
      exact
        explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_bottomIntegralSum_eq_coordinate_of_integrable
          f F hT_nonneg hρ hclosed ha hint
    _ =
        explicitFormulaRectangleBoxBottomEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_bottomEdgeIntegral_eq_coordinate
          f ρ a).symm

/-- Top raw-hole horizontal side telescope after the finite subspan classification has
selected exactly the sorted adjacent intervals contained in that raw square side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_topIntegralSum_eq_coordinate_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  have hfilter :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), y)
            else
              0)
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))), y))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) :=
    explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
      hρ ha (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f) y
  have hsubrange :
      explicitFormulaRectangleListSum
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ
                  (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))), y))
          (List.ofFn
            (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) :=
    explicitFormulaRectangleRawHoleXSubrangeTopHorizontalIntegralSum_eq_coordinate
      f F T hρ ha y hint
  exact Eq.trans hfilter hsubrange

/-- Constructive top raw-hole horizontal side telescope over the generated raw-hole block,
with no predicate-filtered adjacent-pair sum. -/
theorem explicitFormulaRectangleRawHoleXBlockTopContribution_eq_coordinate_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) :
    explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  have hgenerated :
      explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha =
        explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))), y))
          (List.ofFn (fun i : Fin span => i)) := by
    exact congrArg
      (fun g : Fin span → ℂ =>
        explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin span => i)))
      (funext
        (fun i =>
          let xpair := explicitFormulaRectangleRawHoleXAdjacentEndpointPairAt F hρ a ha i
          have hx₀ :
              xpair.x₀ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1) :=
            explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ
              ⟨lo + i.1,
                explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                  F T hρ ha i⟩
          have hx₁_base :
              xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) :=
            explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ
              ⟨lo + i.1,
                explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
                  F T hρ ha i⟩
          have hx₁_index :
              explicitFormulaRectangleSortedXEndpointAt F T ρ ((lo + i.1) + 1) =
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
            congrArg
              (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
              (Nat.add_assoc lo i.1 1)
          have hx₁ :
              xpair.x₁ = explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)) :=
            Eq.trans hx₁_base hx₁_index
          congrArg
            (fun endpoints : ℝ × ℝ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f (endpoints, y))
            (Prod.ext hx₀ hx₁)))
  have hsubrange :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1),
                explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1))), y))
          (List.ofFn (fun i : Fin span => i)) =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) :=
    explicitFormulaRectangleRawHoleXSubrangeTopHorizontalIntegralSum_eq_coordinate
      f F T hρ ha y hint
  exact Eq.trans hgenerated hsubrange

/-- Constructive top raw-hole horizontal side telescope in raw endpoint-data box
normalization. -/
theorem explicitFormulaRectangleRawHoleXBlockTopContribution_eq_rawBoxTop_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) :
    explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha =
      explicitFormulaRectangleBoxTopEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  calc
    explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
      exact
        explicitFormulaRectangleRawHoleXBlockTopContribution_eq_coordinate_of_integrable
          f F hρ ha hint
    _ =
        explicitFormulaRectangleBoxTopEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_topEdgeIntegral_eq_coordinate
          f ρ a).symm

/-- Top raw-hole horizontal side telescope expressed in the raw endpoint-data box
normalization. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_topIntegralSum_eq_rawBoxTop_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBoxTopEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
      exact
        explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_topIntegralSum_eq_coordinate_of_integrable
          f F hT_nonneg hρ hclosed ha hint
    _ =
        explicitFormulaRectangleBoxTopEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_topEdgeIntegral_eq_coordinate
          f ρ a).symm

/-- The sorted horizontal subdivision subspans contained in a raw square side assemble
to the two full horizontal sides of that raw square. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_horizontalIntegralSums_eq_rawBoxSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) →
    (explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) →
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBoxBottomEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a)) ∧
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBoxTopEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a)) := by
  intro hbottom htop
  exact
    And.intro
      (explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_bottomIntegralSum_eq_rawBoxBottom_of_integrable
        f F hT_nonneg hρ hclosed ha hbottom)
      (explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_topIntegralSum_eq_rawBoxTop_of_integrable
        f F hT_nonneg hρ hclosed ha htop)

/-- The sorted horizontal subdivision subspans contained in a raw square side assemble to
that raw square's full bottom side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_bottomIntegralSum_eq_rawBoxBottom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBoxBottomEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  exact
    explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_bottomIntegralSum_eq_rawBoxBottom_of_integrable
      f F hT_nonneg hρ hclosed ha hint

/-- The sorted horizontal subdivision subspans contained in a raw square side assemble to
that raw square's full top side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_topIntegralSum_eq_rawBoxTop
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBoxTopEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
  exact
    explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_topIntegralSum_eq_rawBoxTop_of_integrable
      f F hT_nonneg hρ hclosed ha hint

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
