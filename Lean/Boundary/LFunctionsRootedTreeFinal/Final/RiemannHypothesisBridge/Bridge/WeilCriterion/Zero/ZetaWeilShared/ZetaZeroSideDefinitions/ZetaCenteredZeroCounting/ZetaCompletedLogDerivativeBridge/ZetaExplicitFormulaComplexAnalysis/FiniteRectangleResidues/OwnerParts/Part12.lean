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
  have hcell_group :
      (∑ i in Finset.range cols,
          (bottom i - top i + right i - left i)) =
        ∑ i in Finset.range cols,
          (bottom i - top i + (right i - left i)) := by
    exact Finset.sum_congr rfl
      (fun i _hi =>
        calc
          bottom i - top i + right i - left i =
              (bottom i - top i + right i) + -left i := by
            exact sub_eq_add_neg (bottom i - top i + right i) (left i)
          _ = bottom i - top i + (right i + -left i) := by
            exact add_assoc (bottom i - top i) (right i) (-left i)
          _ = bottom i - top i + (right i - left i) := by
            exact congrArg
              (fun z : ℂ => bottom i - top i + z)
              (sub_eq_add_neg (right i) (left i)).symm)
  have hsplit :
      (∑ i in Finset.range cols,
          (bottom i - top i + right i - left i)) =
        (∑ i in Finset.range cols, (bottom i - top i)) +
          (∑ i in Finset.range cols, (right i - left i)) := by
    calc
      (∑ i in Finset.range cols,
          (bottom i - top i + right i - left i)) =
          ∑ i in Finset.range cols,
            (bottom i - top i + (right i - left i)) := by
        exact hcell_group
      _ =
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
          (Set.uIcc (lower c).re (upper c).re ×ℂ
            Set.uIcc (lower c).im (upper c).im))
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

/-- The oriented boundary integral of a finite punctured rectangle in the residue
normalization used in this owner file.  The outer rectangle is counterclockwise; each
deleted circle is recorded with positive residue orientation and therefore subtracted from
the punctured-domain boundary. -/
noncomputable def finiteRectanglePuncturedBoundaryIntegral
    (S : Finset ℂ) (outer : ℂ) (deletedCircle : ℂ → ℂ) : ℂ :=
  outer - finiteRectangleDeletedCircleBoundarySum S deletedCircle

/-- The positive-orientation deleted-circle boundary contribution of the completed
explicit-formula integrand around a singular coordinate. -/
noncomputable def explicitFormulaRectangleRawDeletedCircleBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) : ℂ :=
  ∮ z in C(a, ε), zetaCompletedExplicitFormulaContourIntegrand f z

/-- The positive-orientation square deleted-boundary contribution of the completed
explicit-formula integrand around a singular coordinate.  This is the rectangular
replacement boundary used by the finite square-hole subdivision before transport back to
the public circular deleted-boundary normalization. -/
noncomputable def explicitFormulaRectangleRawDeletedSquareBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareBoundaryIntegral
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a ε

/-- The positive-orientation inscribed-square deleted-boundary contribution of the
completed explicit-formula integrand around a singular coordinate.  The square half-width
is `ε / 2`, so this boundary is the square-hole replacement compatible with radius-`ε`
closed-disk controls. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareBoundaryIntegral
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a (ε / 2)

/-- The tangent punctured-boundary integral for the completed explicit-formula rectangle
in the tangent-weighted contour normalization used by Cauchy-Goursat. -/
noncomputable def explicitFormulaRectangleTangentPuncturedBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ) : ℂ :=
  finiteRectanglePuncturedBoundaryIntegral S
    (zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T))
    deletedCircle

/-- The finite-radius tangent punctured-boundary integral for the completed explicit
formula, using the actual deleted-circle boundary integrals of the raw integrand. -/
noncomputable def explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) : ℂ :=
  explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
    (explicitFormulaRectangleRawSingularCoordinates T)
    (explicitFormulaRectangleRawDeletedCircleBoundary f ε)

/-- The finite-radius tangent square-punctured boundary for the completed explicit
formula, using square deleted-boundary integrals of the raw integrand. -/
noncomputable def explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) : ℂ :=
  explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
    (explicitFormulaRectangleRawSingularCoordinates T)
    (explicitFormulaRectangleRawDeletedSquareBoundary f ε)

/-- The finite-radius tangent inscribed-square-punctured boundary for the completed
explicit formula, using half-width `ε / 2` square deleted-boundary integrals of the raw
integrand. -/
noncomputable def explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) : ℂ :=
  explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
    (explicitFormulaRectangleRawSingularCoordinates T)
    (explicitFormulaRectangleRawInscribedSquareBoundary f ε)

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
          (Set.uIcc (lower c).re (upper c).re ×ℂ
            Set.uIcc (lower c).im (upper c).im))
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
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) :=
  fun _ hx =>
    And.intro
      (Set.Ioo_subset_Icc_self hx.1)
      (Set.Ioo_subset_Icc_self hx.2)

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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
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
        (Set.uIcc (lower c).re (upper c).re ×ℂ
          Set.uIcc (lower c).im (upper c).im) ⊆
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
          (Set.uIcc (lower c).re (upper c).re ×ℂ
            Set.uIcc (lower c).im (upper c).im) :=
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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
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
        (Set.uIcc (lower c).re (upper c).re ×ℂ
          Set.uIcc (lower c).im (upper c).im) ⊆
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
          (Set.uIcc (lower c).re (upper c).re ×ℂ
            Set.uIcc (lower c).im (upper c).im))
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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
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
        (Set.uIcc (lower c).re (upper c).re ×ℂ
          Set.uIcc (lower c).im (upper c).im) ⊆
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
          (Set.uIcc (lower c).re (upper c).re ×ℂ
            Set.uIcc (lower c).im (upper c).im) :=
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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
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
        (Set.uIcc (lower c).re (upper c).re ×ℂ
          Set.uIcc (lower c).im (upper c).im) ⊆
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
          (Set.uIcc (lower c).re (upper c).re ×ℂ
            Set.uIcc (lower c).im (upper c).im))
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

/-- Lower-left corner of the inscribed square of circular radius `ε` around a raw
singular coordinate. -/
def explicitFormulaRectangleRawInscribedSquareLowerCorner (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareLowerCorner a (ε / 2)

/-- Upper-right corner of the inscribed square of circular radius `ε` around a raw
singular coordinate. -/
def explicitFormulaRectangleRawInscribedSquareUpperCorner (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareUpperCorner a (ε / 2)

/-- The lower-left corner of the raw inscribed square is the lower-left corner of the
ordinary deleted square at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_eq_squareLowerCorner_half
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareLowerCorner ε a =
      finiteRectangleSquareLowerCorner a (ε / 2) := by
  rfl

/-- The upper-right corner of the raw inscribed square is the upper-right corner of the
ordinary deleted square at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_eq_squareUpperCorner_half
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareUpperCorner ε a =
      finiteRectangleSquareUpperCorner a (ε / 2) := by
  rfl

/-- Closed cell of the inscribed square of circular radius `ε` around a raw singular
coordinate. -/
def explicitFormulaRectangleRawInscribedSquareClosedCell (ε : ℝ) (a : ℂ) : Set ℂ :=
  Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ×ℂ
    Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im

/-- The named inscribed-square closed cell is the closed rectangle between the named
lower-left and upper-right corners. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_eq
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareClosedCell ε a =
      (Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ×ℂ
        Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im) := by
  rfl

/-- Transport membership in an unordered closed interval across endpoint equalities. -/
theorem finiteRectangle_mem_uIcc_congr_endpoints
    {x a b c d : ℝ} (ha : a = c) (hb : b = d)
    (hx : x ∈ Set.uIcc a b) :
    x ∈ Set.uIcc c d :=
  match ha, hb with
  | rfl, rfl => hx

/-- Real coordinate of the lower-left corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_re
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re =
      a.re - ε / 2 :=
  finiteRectangleSquareLowerCorner_re a (ε / 2)

/-- Imaginary coordinate of the lower-left corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_im
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im =
      a.im - ε / 2 :=
  finiteRectangleSquareLowerCorner_im a (ε / 2)

/-- Real coordinate of the upper-right corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_re
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re =
      a.re + ε / 2 :=
  finiteRectangleSquareUpperCorner_re a (ε / 2)

/-- Imaginary coordinate of the upper-right corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_im
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im =
      a.im + ε / 2 :=
  finiteRectangleSquareUpperCorner_im a (ε / 2)

/-- The center of a raw inscribed square belongs to its named closed cell. -/
theorem explicitFormulaRectangleRawSingular_mem_own_inscribedSquareClosedCell
    {ε : ℝ} (hε : 0 ≤ ε) (a : ℂ) :
    a ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a := by
  have hε_div_two_nonneg : 0 ≤ ε / 2 :=
    div_nonneg hε zero_le_two
  have hre_left : a.re - ε / 2 ≤ a.re :=
    sub_le_self a.re hε_div_two_nonneg
  have hre_right : a.re ≤ a.re + ε / 2 :=
    le_add_of_nonneg_right hε_div_two_nonneg
  have him_left : a.im - ε / 2 ≤ a.im :=
    sub_le_self a.im hε_div_two_nonneg
  have him_right : a.im ≤ a.im + ε / 2 :=
    le_add_of_nonneg_right hε_div_two_nonneg
  have hre_center :
      a.re ∈ Set.uIcc (a.re - ε / 2) (a.re + ε / 2) :=
    Set.mem_uIcc.mpr (Or.inl (And.intro hre_left hre_right))
  have him_center :
      a.im ∈ Set.uIcc (a.im - ε / 2) (a.im + ε / 2) :=
    Set.mem_uIcc.mpr (Or.inl (And.intro him_left him_right))
  have hre :
      a.re ∈
        Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re :=
    finiteRectangle_mem_uIcc_congr_endpoints
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_re ε a).symm
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_re ε a).symm
      hre_center
  have him :
      a.im ∈
        Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im :=
    finiteRectangle_mem_uIcc_congr_endpoints
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_im ε a).symm
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_im ε a).symm
      him_center
  exact And.intro hre him

/-- A rectangular subdivision cell disjoint from every removed raw inscribed square avoids
the raw singular carrier. -/
theorem explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_disjoint_inscribedSquares
    (T ε : ℝ) (hε : 0 ≤ ε) (lower upper : ℂ)
    (hdisjoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Disjoint
            (Set.uIcc lower.re upper.re ×ℂ Set.uIcc lower.im upper.im)
            (explicitFormulaRectangleRawInscribedSquareClosedCell ε a))
    {z : ℂ}
    (hz : z ∈ (Set.uIcc lower.re upper.re ×ℂ Set.uIcc lower.im upper.im)) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T := by
  intro hzRaw
  have hzOwn :
      z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε z :=
    explicitFormulaRectangleRawSingular_mem_own_inscribedSquareClosedCell hε z
  exact
    (Set.disjoint_left.mp (hdisjoint z hzRaw)) hz hzOwn

/-- A point in a rectangular cell can equal a center only if both center coordinates lie in
the corresponding coordinate intervals. -/
theorem finiteRectangleSubdivisionCell_ne_center_of_coordinate_omission
    (lower upper a z : ℂ)
    (hz : z ∈ (Set.uIcc lower.re upper.re ×ℂ Set.uIcc lower.im upper.im))
    (homit :
      a.re ∉ Set.uIcc lower.re upper.re ∨
        a.im ∉ Set.uIcc lower.im upper.im) :
    z ≠ a := by
  intro hza
  match homit with
  | Or.inl hre_omit =>
      have hre_mem : a.re ∈ Set.uIcc lower.re upper.re :=
        Eq.subst
          (motive := fun w : ℂ => w.re ∈ Set.uIcc lower.re upper.re)
          hza
          hz.1
      exact hre_omit hre_mem
  | Or.inr him_omit =>
      have him_mem : a.im ∈ Set.uIcc lower.im upper.im :=
        Eq.subst
          (motive := fun w : ℂ => w.im ∈ Set.uIcc lower.im upper.im)
          hza
          hz.2
      exact him_omit him_mem

/-- A rectangular subdivision cell avoids the raw finite singular-coordinate carrier when
each raw center is omitted by at least one coordinate interval. -/
theorem explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_coordinate_omission
    (T : ℝ) (lower upper : ℂ)
    (homit :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ Set.uIcc lower.re upper.re ∨
            a.im ∉ Set.uIcc lower.im upper.im)
    {z : ℂ}
    (hz : z ∈ (Set.uIcc lower.re upper.re ×ℂ Set.uIcc lower.im upper.im)) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T := by
  intro hzRaw
  exact
    finiteRectangleSubdivisionCell_ne_center_of_coordinate_omission
      lower upper z z hz (homit z hzRaw) rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
