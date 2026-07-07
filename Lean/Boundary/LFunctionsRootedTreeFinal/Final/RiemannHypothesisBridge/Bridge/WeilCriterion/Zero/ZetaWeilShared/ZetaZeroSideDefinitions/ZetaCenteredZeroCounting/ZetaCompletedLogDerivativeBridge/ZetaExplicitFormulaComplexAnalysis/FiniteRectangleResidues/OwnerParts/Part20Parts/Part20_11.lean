import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_14

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
## Part20 11: VerticalRejectedAndSelectedScan
-/

/-- The proof-carrying regular adjacent endpoint-pair cell determined by a horizontal
adjacent pair, a vertical adjacent pair, and the coordinate-omission proof. -/
def explicitFormulaRectangleRegularAdjacentEndpointPairCellOfOmission
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (homit : explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ρ :=
  { xpair := xpair
    ypair := ypair
    homit := homit }

instance explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission_decidable_part20_11
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    Decidable (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair) := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  let P : ℂ → Prop :=
    fun a : ℂ =>
      ¬
        (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a)
  have hdep :
      Decidable (∀ a : ℂ, ∀ h : a ∈ S, P a) :=
    @Finset.decidableDforallFinset ℂ S
      (fun a _ha => P a)
      (fun a _ha => inferInstance)
  letI : Decidable (∀ a : ℂ, ∀ h : a ∈ S, P a) := hdep
  show Decidable (∀ a : ℂ, a ∈ S → P a)
  exact
    decidable_of_iff
      (∀ a : ℂ, ∀ h : a ∈ S, P a)
      (Iff.intro
        (fun h a ha => h a ha)
        (fun h a ha => h a ha))

/-- A crossed adjacent-pair subspan lies in the named raw closed square at its
lower-left grid corner. -/
theorem explicitFormulaRectangleRawHoleSubspans_lowerLeft_mem_closedCell
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    {xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ}
    {ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ}
    {a : ℂ}
    (hx : explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a)
    (hy : explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a) :
    ({ re := xpair.x₀, im := ypair.y₀ } : ℂ) ∈
      explicitFormulaRectangleRawInscribedSquareClosedCell ρ a := by
  have hxmem :
      ({ re := xpair.x₀, im := ypair.y₀ } : ℂ).re ∈
        Set.uIcc
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re := by
    exact Set.mem_uIcc.mpr
      (Or.inl
        (And.intro hx.1
          (le_trans (le_of_lt xpair.hx_order) hx.2)))
  have hymem :
      ({ re := xpair.x₀, im := ypair.y₀ } : ℂ).im ∈
        Set.uIcc
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im := by
    exact Set.mem_uIcc.mpr
      (Or.inl
        (And.intro hy.1
          (le_trans (le_of_lt ypair.hy_order) hy.2)))
  exact And.intro hxmem hymem

/-- A crossed adjacent-pair subspan can belong to at most one raw square under the
strict closed-radius separation controls. -/
theorem explicitFormulaRectangleRawHoleSubspans_not_ne_of_pairwiseSeparated
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    {xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ}
    {ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ}
    {a b : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hb : b ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hxa : explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a)
    (hya : explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a)
    (hxb : explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair b)
    (hyb : explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair b) :
    a ≠ b → False := by
  intro hab
  let z : ℂ := { re := xpair.x₀, im := ypair.y₀ }
  have hz_a :
      z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ρ a :=
    explicitFormulaRectangleRawHoleSubspans_lowerLeft_mem_closedCell hxa hya
  have hz_b :
      z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ρ b :=
    explicitFormulaRectangleRawHoleSubspans_lowerLeft_mem_closedCell hxb hyb
  have hballs :
      ∀ c : ℂ,
        c ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ d : ℂ,
            d ∈ explicitFormulaRectangleRawSingularCoordinates T →
              c ≠ d →
                Disjoint (Metric.closedBall c ρ) (Metric.closedBall d ρ) := by
    intro c hc d hd hcd
    exact Metric.closedBall_disjoint_closedBall (hsep c hc d hd hcd)
  have hdisj :
      Disjoint
        (explicitFormulaRectangleRawInscribedSquareClosedCell ρ a)
        (explicitFormulaRectangleRawInscribedSquareClosedCell ρ b) :=
    explicitFormulaRectangleRawInscribedSquareClosedCell_pairwiseDisjoint_of_closedRadiusControls
      T ρ (le_of_lt hρ) hballs a ha b hb hab
  exact (Set.disjoint_left.mp hdisj) hz_a hz_b

/-- A rejected endpoint-data cell is counted by exactly the raw square containing its
crossed horizontal and vertical adjacent spans. -/
theorem explicitFormulaRectangleRejectedRawHoleOmission_eq_rawHoleSubspanFinsetSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (g : ℂ)
    [Decidable (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair)]
    [DecidablePred
      (fun a : ℂ =>
        explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a)] :
    (if _homit :
        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
      0
    else
      g) =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
          g
        else
          0 := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  let Q : ℂ → Prop :=
    fun a =>
      explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
        explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a
  match inferInstanceAs
      (Decidable (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair)) with
  | isTrue homit =>
      have hzero :
          (∑ a in S, if _hspan : Q a then g else 0) = 0 := by
        exact Finset.sum_eq_zero
          (fun a ha =>
            match inferInstanceAs (Decidable (Q a)) with
            | isTrue hspan =>
                False.elim (homit a ha hspan)
            | isFalse hspan =>
                if_neg hspan)
      calc
        (if _homit :
            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
          0
        else
          g) = 0 := by
          exact if_pos homit
        _ = ∑ a in S, if _hspan : Q a then g else 0 := by
          exact hzero.symm
  | isFalse homit =>
      have hnot_forall : ¬ ∀ a : ℂ, a ∈ S → ¬ Q a := homit
      have hfilter_ne :
          (S.filter Q) ≠ ∅ := by
        intro hfilter_empty
        have hforall : ∀ a : ℂ, a ∈ S → ¬ Q a := by
          intro a ha hqa
          have hafilter : a ∈ S.filter Q :=
            Finset.mem_filter.mpr (And.intro ha hqa)
          have haempty : a ∈ (∅ : Finset ℂ) := by
            exact Eq.mp (congrArg (fun U : Finset ℂ => a ∈ U) hfilter_empty) hafilter
          exact Finset.not_mem_empty a haempty
        exact hnot_forall hforall
      have hfilter_nonempty : (S.filter Q).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hfilter_ne
      obtain ⟨a, hafilter⟩ := hfilter_nonempty.exists_mem
      have ha : a ∈ S := (Finset.mem_filter.mp hafilter).1
      have hqa : Q a := (Finset.mem_filter.mp hafilter).2
      have hsum :
          (∑ b in S, if _hspan : Q b then g else 0) = g := by
        exact Eq.trans
          (Finset.sum_eq_single a
            (fun b hb hba =>
              match inferInstanceAs (Decidable (Q b)) with
              | isTrue hqb =>
                  have hnot_ne : b ≠ a → False :=
                    fun hne =>
                      explicitFormulaRectangleRawHoleSubspans_not_ne_of_pairwiseSeparated
                        hρ hsep hb ha hqb.1 hqb.2 hqa.1 hqa.2 hne
                  False.elim (hnot_ne hba)
              | isFalse hqb =>
                  if_neg hqb)
            (fun ha_not_mem =>
              False.elim (ha_not_mem ha)))
          (if_pos hqa)
      calc
        (if _homit :
            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
          0
        else
          g) = g := by
          exact if_neg homit
        _ = ∑ a in S, if _hspan : Q a then g else 0 := by
          exact hsum.symm

/-- A rejected endpoint-data cell's paired contribution is counted by the unique raw
square containing its crossed spans. -/
theorem explicitFormulaRectangleRejectedRawHoleOmission_pairContribution_eq_rawHoleSubspanFinsetSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (lower upper : ℂ)
    [Decidable (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair)]
    [DecidablePred
      (fun a : ℂ =>
        explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a)] :
    (if _homit :
        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
      0
    else
      lower - upper) =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
          lower - upper
        else
          0 := by
  exact
    explicitFormulaRectangleRejectedRawHoleOmission_eq_rawHoleSubspanFinsetSum
      hρ hsep xpair ypair (lower - upper)

theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_rightScan_sub_leftScan
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        ypair =
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                xpair ypair homit)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                xpair ypair homit)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let rightScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
          (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
            xpair ypair homit)
      else
        0
  let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
          (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
            xpair ypair homit)
      else
        0
  have hcolumn :
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution f xpairs ypair =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          xpairs :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_listSum
      f ypair xpairs
  have hpoint :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ,
        explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
            f xpair ypair =
          rightScan xpair - leftScan xpair := by
    intro xpair
    match inferInstanceAs
        (Decidable
          (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
    | isTrue homit =>
        have hright :
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                  xpair ypair homit) =
              (if homit' :
                  explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                  (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                    xpair ypair homit')
              else
                0) :=
          by
            have hdif :
                (if homit' :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                    (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                      xpair ypair homit')
                else
                  0) =
                  explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                    (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                      xpair ypair homit) := by
              exact dif_pos homit
            exact hdif.symm
        have hleft :
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                  xpair ypair homit) =
              (if homit' :
                  explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                  (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                    xpair ypair homit')
              else
                0) :=
          by
            have hdif :
                (if homit' :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                    (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                      xpair ypair homit')
                else
                  0) =
                  explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                    (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                      xpair ypair homit) := by
              exact dif_pos homit
            exact hdif.symm
        calc
          explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair =
              explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                  xpair ypair homit) -
                explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                  (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                    xpair ypair homit) := by
            exact dif_pos homit
          _ = rightScan xpair - leftScan xpair := by
            exact congrArg₂ HSub.hSub hright hleft
    | isFalse homit =>
        have hright :
            0 =
              (if homit' :
                  explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                  (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                    xpair ypair homit')
              else
                0) :=
          by
            have hdif :
                (if homit' :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                    (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                      xpair ypair homit')
                else
                  0) =
                  0 := by
              exact dif_neg homit
            exact hdif.symm
        have hleft :
            0 =
              (if homit' :
                  explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                  (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                    xpair ypair homit')
              else
                0) :=
          by
            have hdif :
                (if homit' :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                    (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
                      xpair ypair homit')
                else
                  0) =
                  0 := by
              exact dif_neg homit
            exact hdif.symm
        calc
          explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair = 0 := by
            exact dif_neg homit
          _ = rightScan xpair - leftScan xpair := by
            exact Eq.trans (sub_zero (0 : ℂ)).symm
              (congrArg₂ HSub.hSub hright hleft)
  have hreplace :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            rightScan xpair - leftScan xpair)
          xpairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
        explicitFormulaRectangleListSum g xpairs)
      (funext hpoint)
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution f xpairs ypair =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          xpairs := by
      exact hcolumn
    _ =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            rightScan xpair - leftScan xpair)
          xpairs := by
      exact hreplace
    _ =
        explicitFormulaRectangleListSum rightScan xpairs -
          explicitFormulaRectangleListSum leftScan xpairs := by
      exact explicitFormulaRectangleListSum_sub rightScan leftScan xpairs

/-- The paired selected vertical coordinate-label sums are exactly the selected
fixed-column endpoint-data contribution.  This isolates the remaining geometric
exposure work from the coordinate/list transport. -/
theorem explicitFormulaRectangleSelectedVerticalEdgeCoordinatesOfFixedY_integralSum_eq_columnContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          ypair) -
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          ypair) =
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        ypair := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let rightScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
            (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
              xpair ypair homit)
        else
          0)
      xpairs
  let leftScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
            (explicitFormulaRectangleSelectedFixedYAdjacentEndpointData
              xpair ypair homit)
        else
          0)
      xpairs
  have hright :
      rightScan =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair) :=
    explicitFormulaRectangleSelectedFixedY_rightScan_eq_coordinateIntegralSum
      f xpairs ypair
  have hleft :
      leftScan =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) :=
    explicitFormulaRectangleSelectedFixedY_leftScan_eq_coordinateIntegralSum
      f xpairs ypair
  have hcolumn :
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
          f xpairs ypair =
        rightScan - leftScan :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_rightScan_sub_leftScan
      f F ypair
  calc
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair) -
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) =
        rightScan -
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair))
        hright.symm
    _ = rightScan - leftScan := by
      exact congrArg (fun z : ℂ => rightScan - z) hleft.symm
    _ =
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
          f xpairs ypair := by
      exact hcolumn.symm

/-- Fixed-column rejected vertical scan grouping.  The non-selected right-minus-left
horizontal adjacent-pair scan is exactly the sum of raw-hole right-minus-left slices
whose vertical span contains the fixed `ypair`. -/
theorem explicitFormulaRectangleRejectedEndpointDataVerticalColumnScanSub_eq_holeSub
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            0
          else
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
        else
          0) -
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let contribution : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₁) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₀)
  let rawContribution : ℂ → ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun a xpair =>
      if _hspan :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
        contribution xpair
      else
        0
  have hclassified :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              0
            else
              contribution xpair)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            ∑ a in S, rawContribution a xpair)
          xpairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
        explicitFormulaRectangleListSum g xpairs)
      (funext
        (fun xpair =>
          explicitFormulaRectangleRejectedRawHoleOmission_pairContribution_eq_rawHoleSubspanFinsetSum
            hρ hsep xpair ypair
            (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁))
            (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀))))
  have hcommute :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            ∑ a in S, rawContribution a xpair)
          xpairs =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rawContribution a xpair)
            xpairs :=
    explicitFormulaRectangleListSum_finset_sum
      S
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        fun a : ℂ => rawContribution a xpair)
      xpairs
  have hraw :
      (∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rawContribution a xpair)
            xpairs) =
        ∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0 := by
    exact Finset.sum_congr (Eq.refl S)
      (fun a ha => by
          match inferInstanceAs
              (Decidable
                (explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a)) with
          | isTrue hy =>
            let xOnly : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
              fun xpair =>
                if _hx :
                    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                  contribution xpair
                else
                  0
            have hreduce :
                explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      rawContribution a xpair)
                    xpairs =
                  explicitFormulaRectangleListSum xOnly xpairs := by
              exact congrArg
                (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
                  explicitFormulaRectangleListSum g xpairs)
                (funext
                  (fun xpair =>
                    by
                      match inferInstanceAs
                          (Decidable
                            (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                              ρ xpair a)) with
                      | isTrue hx =>
                        calc
                          rawContribution a xpair = contribution xpair := by
                            exact if_pos (And.intro hx hy)
                          _ = xOnly xpair := by
                            exact (if_pos hx).symm
                      | isFalse hx =>
                        have hnot :
                            ¬
                              (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                                  ρ xpair a ∧
                                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                                  ρ ypair a) :=
                            fun hboth => hx hboth.1
                        calc
                          rawContribution a xpair = 0 := by
                            exact if_neg hnot
                          _ = xOnly xpair := by
                            exact (if_neg hx).symm))
            have hblock :
                explicitFormulaRectangleListSum xOnly xpairs =
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) :=
              explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_verticalScanSub_eq_rawSides
                f F hρ ha ypair
            calc
              explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    rawContribution a xpair)
                  xpairs =
                  explicitFormulaRectangleListSum xOnly xpairs := by
                exact hreduce
              _ =
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
                exact hblock
              _ =
                  (if _hspan :
                      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
                  else
                    0) := by
                exact (if_pos hy).symm
          | isFalse hy =>
            have hzero :
                explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      rawContribution a xpair)
                    xpairs =
                  0 := by
              have hfun :
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      rawContribution a xpair) =
                    (fun _xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      (0 : ℂ)) := by
                exact funext
                  (fun xpair =>
                    by
                      have hnot :
                          ¬
                            (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                                ρ xpair a ∧
                              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                                ρ ypair a) :=
                          fun hboth => hy hboth.2
                      exact if_neg hnot)
              exact Eq.trans
                (congrArg
                  (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
                    explicitFormulaRectangleListSum g xpairs)
                  hfun)
                (explicitFormulaRectangleListSum_zero xpairs)
            calc
              explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    rawContribution a xpair)
                  xpairs = 0 := by
                exact hzero
              _ =
                  (if _hspan :
                      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
                  else
                    0) := by
                exact (if_neg hy).symm)
  have hsplit :
      (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
    have hpoint :
        ∀ a : ℂ,
          (if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) =
            (if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0) -
              (if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
              else
                0) := by
      intro a
      match inferInstanceAs
          (Decidable
            (explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a)) with
      | isTrue hy =>
          exact
            Eq.trans (if_pos hy)
              (congrArg₂ HSub.hSub
                (if_pos hy).symm
                (if_pos hy).symm)
      | isFalse hy =>
          exact
            Eq.trans (if_neg hy)
              (Eq.trans (sub_zero (0 : ℂ)).symm
                (congrArg₂ HSub.hSub
                  (if_neg hy).symm
                  (if_neg hy).symm))
    calc
      (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) =
          ∑ a in S,
            ((if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0) -
              (if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
              else
                0)) := by
        exact Finset.sum_congr (Eq.refl S) (fun a _ha => hpoint a)
      _ =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
        exact Finset.sum_sub_distrib
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            0
          else
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀))
        xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            ∑ a in S, rawContribution a xpair)
          xpairs := by
      exact hclassified
    _ =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rawContribution a xpair)
            xpairs := by
      exact hcommute
    _ =
        ∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0 := by
      exact hraw
    _ =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
      exact hsplit

/-- Fixed-column paired vertical scan partition.  On a fixed vertical adjacent span, the
selected right-minus-left vertical scans are the full outer right-minus-left scan with
exactly the raw-hole right-minus-left scans removed. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnScanSub_eq_outerSub_sub_holeSub
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
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)) -
      (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)) =
      (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), F.c) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), 1 - F.c)) -
        ((∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let P : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → Prop :=
    fun xpair => explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair
  let rightCoord : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((ypair.y₀, ypair.y₁), xpair.x₁)
  let leftCoord : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((ypair.y₀, ypair.y₁), xpair.x₀)
  have hcell_right :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then rightCoord xpair else 0)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then rightCoord xpair else 0)
          xpairs :=
    Eq.refl _
  have hcell_left :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then leftCoord xpair else 0)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then leftCoord xpair else 0)
          xpairs :=
    Eq.refl _
  have hselected :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then rightCoord xpair else 0)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then leftCoord xpair else 0)
          xpairs =
        (explicitFormulaRectangleListSum rightCoord xpairs -
          explicitFormulaRectangleListSum leftCoord xpairs) -
          (explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit : P xpair then 0 else leftCoord xpair)
              xpairs) :=
    explicitFormulaRectangleListSum_selectSub_eq_totalSub_sub_rejectSub
      P rightCoord leftCoord xpairs
  have htotal :
      explicitFormulaRectangleListSum rightCoord xpairs -
          explicitFormulaRectangleListSum leftCoord xpairs =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c) -
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c) :=
    explicitFormulaRectangleXAdjacentEndpointPair_totalVerticalScanSub_eq_outerSub
      f F hρ hclosed ypair
  have hrejected :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else rightCoord xpair)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else leftCoord xpair)
          xpairs =
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
    have hcombine :
        explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else leftCoord xpair)
            xpairs =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair)
            xpairs := by
      let rejectRight : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
        fun xpair => if _homit : P xpair then 0 else rightCoord xpair
      let rejectLeft : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
        fun xpair => if _homit : P xpair then 0 else leftCoord xpair
      have hsub :
          explicitFormulaRectangleListSum rejectRight xpairs -
              explicitFormulaRectangleListSum rejectLeft xpairs =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                rejectRight xpair - rejectLeft xpair)
              xpairs :=
        (explicitFormulaRectangleListSum_sub rejectRight rejectLeft xpairs).symm
      have hpoint :
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rejectRight xpair - rejectLeft xpair) =
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair) := by
        exact funext
          (fun xpair =>
            by
            match inferInstanceAs (Decidable (P xpair)) with
            | isTrue homit =>
                calc
                  rejectRight xpair - rejectLeft xpair = 0 - 0 := by
                    exact congrArg₂ HSub.hSub (if_pos homit) (if_pos homit)
                  _ = 0 := by
                    exact sub_zero (0 : ℂ)
                  _ = (if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair) := by
                    exact (if_pos homit).symm
            | isFalse homit =>
                calc
                  rejectRight xpair - rejectLeft xpair =
                      rightCoord xpair - leftCoord xpair := by
                    exact congrArg₂ HSub.hSub (if_neg homit) (if_neg homit)
                  _ = (if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair) := by
                    exact (if_neg homit).symm)
      exact Eq.trans hsub
        (congrArg
          (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
            explicitFormulaRectangleListSum g xpairs)
          hpoint)
    calc
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else rightCoord xpair)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else leftCoord xpair)
          xpairs =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair)
            xpairs := by
        exact hcombine
      _ =
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0) -
            (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
              if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
              else
                0) := by
        exact explicitFormulaRectangleRejectedEndpointDataVerticalColumnScanSub_eq_holeSub
          f F hρ hsep ypair
  calc
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit : P xpair then
            rightCoord xpair
          else
            0)
        xpairs) -
      (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit : P xpair then
            leftCoord xpair
          else
            0)
        xpairs) =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then rightCoord xpair else 0)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then leftCoord xpair else 0)
          xpairs := by
      exact congrArg₂ HSub.hSub hcell_right hcell_left
    _ =
        (explicitFormulaRectangleListSum rightCoord xpairs -
          explicitFormulaRectangleListSum leftCoord xpairs) -
          (explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit : P xpair then 0 else leftCoord xpair)
              xpairs) := by
      exact hselected
    _ =
        (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c) -
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c)) -
        (explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else leftCoord xpair)
            xpairs) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            (explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit : P xpair then 0 else rightCoord xpair)
              xpairs -
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  if _homit : P xpair then 0 else leftCoord xpair)
                xpairs))
        htotal
    _ =
      (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), F.c) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), 1 - F.c)) -
        ((∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), F.c) -
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), 1 - F.c)) - z)
        hrejected

/-- Fixed-column vertical coordinate-omission partition.  For one vertical adjacent
slice, the selected right-minus-left scan over horizontal adjacent pairs is the full
outer right-minus-left slice with exactly the raw square-hole subspans removed. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice_of_coordinateOmissionPartition
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
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
        explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let outerRight : ℂ :=
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
      f ((ypair.y₀, ypair.y₁), F.c)
  let outerLeft : ℂ :=
    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
      f ((ypair.y₀, ypair.y₁), 1 - F.c)
  let holeRight : ℂ :=
    ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
      if _hspan :
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
      else
        0
  let holeLeft : ℂ :=
    ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
      if _hspan :
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
      else
        0
  let rightScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if _homit :
            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), xpair.x₁)
        else
          0)
      xpairs
  let leftScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if _homit :
            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), xpair.x₀)
        else
          0)
      xpairs
  have hscan :
      rightScan - leftScan =
        (outerRight - outerLeft) - (holeRight - holeLeft) :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnScanSub_eq_outerSub_sub_holeSub
      f F hT_nonneg hρ hclosed hsep ypair
  have houter :
      explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair =
        outerRight - outerLeft := by
    exact Eq.refl _
  have hhole :
      explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair =
        holeRight - holeLeft :=
    explicitFormulaRectangleVerticalHoleSliceContribution_eq_right_sub_left f T ρ ypair
  calc
    rightScan - leftScan =
        rightScan - leftScan := by
      exact Eq.refl _
    _ = (outerRight - outerLeft) - (holeRight - holeLeft) := by
      exact hscan
    _ =
        explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
          (holeRight - holeLeft) := by
      exact congrArg (fun z : ℂ => z - (holeRight - holeLeft)) houter.symm
    _ =
        explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
          explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair - z)
        hhole.symm

/-- Fixed-column vertical selected contribution collapses to the local outer vertical
slice minus the local square-hole vertical slices. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice
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
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
        explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair := by
  exact
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice_of_coordinateOmissionPartition
      f F hT_nonneg hρ hclosed hsep ypair

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
