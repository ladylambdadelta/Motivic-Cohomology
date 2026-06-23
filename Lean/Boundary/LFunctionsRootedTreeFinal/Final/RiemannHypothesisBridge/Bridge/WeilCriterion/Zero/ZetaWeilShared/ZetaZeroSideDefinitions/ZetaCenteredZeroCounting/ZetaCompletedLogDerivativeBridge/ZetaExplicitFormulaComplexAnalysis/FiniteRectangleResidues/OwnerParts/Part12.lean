import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part11

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

/-- Summing collapsed column boundaries groups the outer horizontal endpoint sums and
the two vertical side sums.  This is the column-wise endpoint algebra used after all
internal horizontal grid edges have cancelled. -/
theorem finiteRectangleSubdivisionCollapsedColumnsBoundary_sum_range
    (bottom top right left : ℕ → ℂ)
    (cols : ℕ) :
    (∑ i in Finset.range cols,
        (bottom i - top i + right i - left i)) =
      (∑ i in Finset.range cols, bottom i) -
        (∑ i in Finset.range cols, top i) +
          ((∑ i in Finset.range cols, right i) -
            (∑ i in Finset.range cols, left i)) := by
  let B : ℂ := ∑ i in Finset.range cols, bottom i
  let U : ℂ := ∑ i in Finset.range cols, top i
  let R : ℂ := ∑ i in Finset.range cols, right i
  let L : ℂ := ∑ i in Finset.range cols, left i
  have hsplit :
      (∑ i in Finset.range cols,
          (bottom i - top i + right i - left i)) =
        (∑ i in Finset.range cols, (bottom i - top i)) +
          (∑ i in Finset.range cols, (right i - left i)) := by
    exact
      Finset.sum_add_distrib
        (s := Finset.range cols)
        (f := fun i : ℕ => bottom i - top i)
        (g := fun i : ℕ => right i - left i)
  have hbottom_top :
      (∑ i in Finset.range cols, (bottom i - top i)) = B - U := by
    calc
      (∑ i in Finset.range cols, (bottom i - top i)) =
          (∑ i in Finset.range cols, (bottom i + -top i)) := by
        exact Finset.sum_congr rfl
          (fun i _hi => sub_eq_add_neg (bottom i) (top i))
      _ =
          (∑ i in Finset.range cols, bottom i) +
            (∑ i in Finset.range cols, -top i) := by
        exact Finset.sum_add_distrib
          (s := Finset.range cols)
          (f := bottom)
          (g := fun i : ℕ => -top i)
      _ =
          (∑ i in Finset.range cols, bottom i) +
            -(∑ i in Finset.range cols, top i) := by
        exact congrArg
          (fun z : ℂ => (∑ i in Finset.range cols, bottom i) + z)
          (Finset.sum_neg_distrib)
      _ = B - U := by
        exact (sub_eq_add_neg B U).symm
  have hright_left :
      (∑ i in Finset.range cols, (right i - left i)) = R - L := by
    calc
      (∑ i in Finset.range cols, (right i - left i)) =
          (∑ i in Finset.range cols, (right i + -left i)) := by
        exact Finset.sum_congr rfl
          (fun i _hi => sub_eq_add_neg (right i) (left i))
      _ =
          (∑ i in Finset.range cols, right i) +
            (∑ i in Finset.range cols, -left i) := by
        exact Finset.sum_add_distrib
          (s := Finset.range cols)
          (f := right)
          (g := fun i : ℕ => -left i)
      _ =
          (∑ i in Finset.range cols, right i) +
            -(∑ i in Finset.range cols, left i) := by
        exact congrArg
          (fun z : ℂ => (∑ i in Finset.range cols, right i) + z)
          (Finset.sum_neg_distrib)
      _ = R - L := by
        exact (sub_eq_add_neg R L).symm
  calc
    (∑ i in Finset.range cols,
        (bottom i - top i + right i - left i)) =
        (∑ i in Finset.range cols, (bottom i - top i)) +
          (∑ i in Finset.range cols, (right i - left i)) := by
      exact hsplit
    _ = (B - U) + (∑ i in Finset.range cols, (right i - left i)) := by
      exact congrArg
        (fun z : ℂ => z + (∑ i in Finset.range cols, (right i - left i)))
        hbottom_top
    _ = (B - U) + (R - L) := by
      exact congrArg (fun z : ℂ => (B - U) + z) hright_left
    _ =
      (∑ i in Finset.range cols, bottom i) -
        (∑ i in Finset.range cols, top i) +
          ((∑ i in Finset.range cols, right i) -
            (∑ i in Finset.range cols, left i)) := by
      rfl

/-- Collapsed column boundaries with all four edge families already identified with their
outer edge integrals. -/
theorem finiteRectangleSubdivisionCollapsedColumnsBoundary_sum_range_of_edge_splits
    (bottom top right left : ℕ → ℂ)
    (cols : ℕ)
    (bottomOuter topOuter rightOuter leftOuter : ℂ)
    (hbottom : (∑ i in Finset.range cols, bottom i) = bottomOuter)
    (htop : (∑ i in Finset.range cols, top i) = topOuter)
    (hright : (∑ i in Finset.range cols, right i) = rightOuter)
    (hleft : (∑ i in Finset.range cols, left i) = leftOuter) :
    (∑ i in Finset.range cols,
        (bottom i - top i + right i - left i)) =
      bottomOuter - topOuter + (rightOuter - leftOuter) := by
  have hcolumn :
      (∑ i in Finset.range cols,
          (bottom i - top i + right i - left i)) =
        (∑ i in Finset.range cols, bottom i) -
          (∑ i in Finset.range cols, top i) +
            ((∑ i in Finset.range cols, right i) -
              (∑ i in Finset.range cols, left i)) :=
    finiteRectangleSubdivisionCollapsedColumnsBoundary_sum_range
      bottom top right left cols
  calc
    (∑ i in Finset.range cols,
        (bottom i - top i + right i - left i)) =
        (∑ i in Finset.range cols, bottom i) -
          (∑ i in Finset.range cols, top i) +
            ((∑ i in Finset.range cols, right i) -
              (∑ i in Finset.range cols, left i)) := by
      exact hcolumn
    _ =
        bottomOuter -
          (∑ i in Finset.range cols, top i) +
            ((∑ i in Finset.range cols, right i) -
              (∑ i in Finset.range cols, left i)) := by
      exact congrArg
        (fun z : ℂ =>
          z - (∑ i in Finset.range cols, top i) +
            ((∑ i in Finset.range cols, right i) -
              (∑ i in Finset.range cols, left i)))
        hbottom
    _ =
        bottomOuter - topOuter +
            ((∑ i in Finset.range cols, right i) -
              (∑ i in Finset.range cols, left i)) := by
      exact congrArg
        (fun z : ℂ =>
          bottomOuter - z +
            ((∑ i in Finset.range cols, right i) -
              (∑ i in Finset.range cols, left i)))
        htop
    _ =
        bottomOuter - topOuter +
            (rightOuter - (∑ i in Finset.range cols, left i)) := by
      exact congrArg
        (fun z : ℂ =>
          bottomOuter - topOuter +
            (z - (∑ i in Finset.range cols, left i)))
        hright
    _ =
        bottomOuter - topOuter + (rightOuter - leftOuter) := by
      exact congrArg
        (fun z : ℂ => bottomOuter - topOuter + (rightOuter - z))
        hleft

/-- Two adjacent coordinate-edge interval integrals combine into the integral over their
outer endpoints. -/
theorem finiteRectangleSubdivisionIntervalIntegral_split_two
    (φ : ℝ → ℂ) (a b c : ℝ)
    (hab : IntervalIntegrable φ volume a b)
    (hbc : IntervalIntegrable φ volume b c) :
    (∫ x : ℝ in a..b, φ x) + (∫ x : ℝ in b..c, φ x) =
      ∫ x : ℝ in a..c, φ x :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- Two adjacent vertical coordinate-edge interval integrals combine after applying the
standard tangent factor `I`. -/
theorem finiteRectangleSubdivisionVerticalIntegral_split_two
    (φ : ℝ → ℂ) (a b c : ℝ)
    (hab : IntervalIntegrable φ volume a b)
    (hbc : IntervalIntegrable φ volume b c) :
    Complex.I • ((∫ y : ℝ in a..b, φ y) + (∫ y : ℝ in b..c, φ y)) =
      Complex.I • (∫ y : ℝ in a..c, φ y) :=
  congrArg
    (fun z : ℂ => Complex.I • z)
    (finiteRectangleSubdivisionIntervalIntegral_split_two
      φ a b c hab hbc)

/-- A finite rectangular subdivision has zero total boundary when each cell satisfies the
rectangular Cauchy-Goursat hypotheses. -/
theorem finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellCauchy
    {ι : Type*} (cells : Finset ι) (g : ℂ → ℂ)
    (lower upper : ι → ℂ)
    (s : ι → Set ℂ)
    (hs : ∀ c : ι, c ∈ cells → (s c).Countable)
    (Hc :
      ∀ c : ι, c ∈ cells →
        ContinuousOn g
          ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]))
    (Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ g x) :
    (∑ c in cells,
        finiteRectangleSubdivisionCellBoundaryIntegral g (lower c) (upper c)) = 0 := by
  exact
    finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellBoundaries
      cells
      (fun c : ι =>
        finiteRectangleSubdivisionCellBoundaryIntegral g (lower c) (upper c))
      (fun c hc =>
        finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
          g (lower c) (upper c) (s c) (hs c hc) (Hc c hc) (Hd c hc))

/-- Transport zero from a concrete finite subdivision boundary sum to the finite-radius
punctured rectangle boundary expression.  The equality hypothesis is the genuine
geometric edge-cancellation theorem: the finite sum of cell boundaries leaves exactly the
outer tangent rectangle boundary minus the positive-orientation deleted-circle sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_subdivisionBoundary
    {ι : Type*} (cells : Finset ι)
    (cellBoundary : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε =
        ∑ c in cells, cellBoundary c)
    (hcellZero : ∀ c : ι, c ∈ cells → cellBoundary c = 0) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 := by
  have hsum :
      (∑ c in cells, cellBoundary c) = 0 :=
    finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellBoundaries
      cells cellBoundary hcellZero
  calc
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε =
        ∑ c in cells, cellBoundary c := by
      exact hsubdivision
    _ = 0 := by
      exact hsum

/-- Cauchy-Goursat zero for the finite-radius punctured rectangle, once the concrete
subdivision geometry has identified the public punctured-boundary expression with a finite
sum of regular rectangular cell boundaries. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_cellCauchy
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (s : ι → Set ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hs : ∀ c : ι, c ∈ cells → (s c).Countable)
    (Hc :
      ∀ c : ι, c ∈ cells →
        ContinuousOn
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]))
    (Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 := by
  have hsum :
      (∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c)) = 0 :=
    finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellCauchy
      cells
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      lower upper s hs Hc Hd
  calc
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c) := by
      exact hsubdivision
	    _ = 0 := by
	      exact hsum

/-- The open rectangle of a subdivision cell is contained in its closed rectangle. -/
theorem finiteRectangleSubdivisionOpenCell_subset_closedCell (z w : ℂ) :
    (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Set.Ioo (min z.im w.im) (max z.im w.im)) ⊆
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
  fun x hx =>
    And.intro
      (Ioo_subset_Icc_self hx.1)
      (Ioo_subset_Icc_self hx.2)

/-- Cauchy-Goursat zero for the finite-radius punctured rectangle from a concrete
subdivision by regular rectangular cells contained in the raw punctured interior.  The
remaining geometric content is exactly the subdivision equality and the cell-containment
proofs. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_rawPuncturedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_closed :
      ∀ c : ι, c ∈ cells →
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]]) ⊆
          finiteRectanglePuncturedDomain
            (explicitFormulaContourFamilyInterior F T)
            (explicitFormulaRectangleRawSingularCoordinates T)
            ε)
    (hcell_open :
      ∀ c : ι, c ∈ cells →
        (Set.Ioo (min (lower c).re (upper c).re)
            (max (lower c).re (upper c).re) ×ℂ
          Set.Ioo (min (lower c).im (upper c).im)
            (max (lower c).im (upper c).im)) ⊆
          finiteRectanglePuncturedDomain
            (explicitFormulaContourFamilyInterior F T)
            (explicitFormulaRectangleRawSingularCoordinates T)
            ε) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 := by
  let s : ι → Set ℂ := fun _ => completedZetaContourIntegrandSingularSet
  have hs : ∀ c : ι, c ∈ cells → (s c).Countable :=
    fun _ _ => completedZetaContourIntegrandSingularSet_countable
  have Hc :
      ∀ c : ι, c ∈ cells →
        ContinuousOn
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) :=
    fun c hc =>
      (explicitFormulaRectangleRawPuncturedInterior_continuousOn
        f F h hT hε hinterior).mono
        (hcell_closed c hc)
  have Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x :=
    fun c hc x hx =>
      explicitFormulaRectangleRawPuncturedInterior_differentiableAt
        f F h hT hε hinterior
        (hcell_open c hc hx.1)
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_cellCauchy
      cells lower upper s f F T ε hsubdivision hs Hc Hd

/-- Cauchy-Goursat zero for the finite-radius punctured rectangle from a concrete
subdivision by rectangular cells whose closed rectangles lie in the raw punctured
interior.  The open-cell differentiability condition follows from closed-cell
containment. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_rawPuncturedClosedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_closed :
      ∀ c : ι, c ∈ cells →
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]]) ⊆
          finiteRectanglePuncturedDomain
            (explicitFormulaContourFamilyInterior F T)
            (explicitFormulaRectangleRawSingularCoordinates T)
            ε) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_rawPuncturedSubdivision
    cells lower upper f F h hT hε hinterior hsubdivision hcell_closed
    (fun c hc =>
      Set.Subset.trans
        (finiteRectangleSubdivisionOpenCell_subset_closedCell (lower c) (upper c))
        (hcell_closed c hc))

/-- Transport zero from a concrete finite subdivision boundary sum to the finite-radius
square-punctured rectangle boundary expression.  The equality hypothesis is the square-hole
edge-cancellation theorem: the finite sum of cell boundaries leaves exactly the outer
tangent rectangle boundary minus the positive-orientation square deleted-boundary sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_zero_of_subdivisionBoundary
    {ι : Type*} (cells : Finset ι)
    (cellBoundary : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells, cellBoundary c)
    (hcellZero : ∀ c : ι, c ∈ cells → cellBoundary c = 0) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε = 0 := by
  have hsum :
      (∑ c in cells, cellBoundary c) = 0 :=
    finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellBoundaries
      cells cellBoundary hcellZero
  calc
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells, cellBoundary c := by
      exact hsubdivision
    _ = 0 := by
      exact hsum

/-- Cauchy-Goursat zero for the finite-radius square-punctured rectangle, once the
concrete square-hole subdivision geometry has identified the public square-punctured
boundary expression with a finite sum of regular rectangular cell boundaries. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_zero_of_cellCauchy
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (s : ι → Set ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hs : ∀ c : ι, c ∈ cells → (s c).Countable)
    (Hc :
      ∀ c : ι, c ∈ cells →
        ContinuousOn
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]))
    (Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε = 0 := by
  have hsum :
      (∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c)) = 0 :=
    finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellCauchy
      cells
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      lower upper s hs Hc Hd
  calc
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c) := by
      exact hsubdivision
    _ = 0 := by
      exact hsum

/-- Cauchy-Goursat zero for the finite-radius square-punctured rectangle from a concrete
subdivision by regular rectangular cells contained in the raw punctured interior.  The
remaining geometric content is exactly the square-hole subdivision equality and the
cell-containment proofs. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_zero_of_rawPuncturedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_closed :
      ∀ c : ι, c ∈ cells →
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]]) ⊆
          finiteRectanglePuncturedDomain
            (explicitFormulaContourFamilyInterior F T)
            (explicitFormulaRectangleRawSingularCoordinates T)
            ε)
    (hcell_open :
      ∀ c : ι, c ∈ cells →
        (Set.Ioo (min (lower c).re (upper c).re)
            (max (lower c).re (upper c).re) ×ℂ
          Set.Ioo (min (lower c).im (upper c).im)
            (max (lower c).im (upper c).im)) ⊆
          finiteRectanglePuncturedDomain
            (explicitFormulaContourFamilyInterior F T)
            (explicitFormulaRectangleRawSingularCoordinates T)
            ε) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε = 0 := by
  let s : ι → Set ℂ := fun _ => completedZetaContourIntegrandSingularSet
  have hs : ∀ c : ι, c ∈ cells → (s c).Countable :=
    fun _ _ => completedZetaContourIntegrandSingularSet_countable
  have Hc :
      ∀ c : ι, c ∈ cells →
        ContinuousOn
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) :=
    fun c hc =>
      (explicitFormulaRectangleRawPuncturedInterior_continuousOn
        f F h hT hε hinterior).mono
        (hcell_closed c hc)
  have Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x :=
    fun c hc x hx =>
      explicitFormulaRectangleRawPuncturedInterior_differentiableAt
        f F h hT hε hinterior
        (hcell_open c hc hx.1)
  exact
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_zero_of_cellCauchy
      cells lower upper s f F T ε hsubdivision hs Hc Hd

/-- Cauchy-Goursat zero for the finite-radius square-punctured rectangle from a concrete
subdivision by rectangular cells whose closed rectangles lie in the raw punctured interior.
The open-cell differentiability condition follows from closed-cell containment. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_zero_of_rawPuncturedClosedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_closed :
      ∀ c : ι, c ∈ cells →
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]]) ⊆
          finiteRectanglePuncturedDomain
            (explicitFormulaContourFamilyInterior F T)
            (explicitFormulaRectangleRawSingularCoordinates T)
            ε) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_zero_of_rawPuncturedSubdivision
    cells lower upper f F h hT hε hinterior hsubdivision hcell_closed
    (fun c hc =>
      Set.Subset.trans
        (finiteRectangleSubdivisionOpenCell_subset_closedCell (lower c) (upper c))
        (hcell_closed c hc))

/-- Cauchy-Goursat zero for the finite-radius inscribed-square-punctured rectangle, once
the concrete inscribed-square subdivision geometry has identified the public
inscribed-square-punctured boundary expression with a finite sum of regular rectangular
cell boundaries. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_cellCauchy
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (s : ι → Set ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hs : ∀ c : ι, c ∈ cells → (s c).Countable)
    (Hc :
      ∀ c : ι, c ∈ cells →
        ContinuousOn
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]))
    (Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 := by
  have hsum :
      (∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c)) = 0 :=
    finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellCauchy
      cells
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      lower upper s hs Hc Hd
  calc
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c) := by
      exact hsubdivision
    _ = 0 := by
      exact hsum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
