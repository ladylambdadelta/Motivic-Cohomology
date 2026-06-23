import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part22

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

/-- Boundary of a constructed regular grid cell is the boundary of its concrete adjacent
rectangle.  Finite sums over supplied regular-cell families use this pointwise theorem via
`explicitFormulaRectangleRegularGridCellBoundarySum_eq_sum_of_forall_mem`. -/
theorem explicitFormulaRectangleRegularGridCellBoundary_ofAdjacentEndpoints
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : x₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hx₁ : x₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hy₀ : y₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hy₁ : y₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hx_order : x₀ < x₁)
    (hy_order : y₀ < y₁)
    (hx_adj : explicitFormulaRectangleNoIntermediateXEndpoint F T ε x₀ x₁)
    (hy_adj : explicitFormulaRectangleNoIntermediateYEndpoint T ε y₀ y₁)
    (homit :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ [[x₀, x₁]] ∨ a.im ∉ [[y₀, y₁]]) :
    finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints
          F T ε x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁
          hx_order hy_order hx_adj hy_adj homit).lower
        (explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints
          F T ε x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁
          hx_order hy_order hx_adj hy_adj homit).upper =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I)
        ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) := by
  exact congrArg₂
    (fun lower upper : ℂ =>
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        lower upper)
    (explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints_lower
      F T ε x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁
      hx_order hy_order hx_adj hy_adj homit)
    (explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints_upper
      F T ε x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁
      hx_order hy_order hx_adj hy_adj homit)

/-- Cauchy-Goursat zero for an inscribed-square-punctured rectangle from a finite family
of proof-carrying regular grid cells.  This is the regularity consumer closest to the
eventual concrete finite complement subdivision: the remaining geometric input is the
boundary equality plus location of closed/open cells relative to the outer rectangle. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridCellSubtype
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T ε))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            c.lower c.upper)
    (hcell_location :
      ∀ c : ExplicitFormulaRectangleRegularGridCell F T ε, c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ c.lower.re, c.upper.re ]] ×ℂ [[ c.lower.im, c.upper.im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T ∨
              z ∈ explicitFormulaContourFamilyBoundary F T)
    (hcell_open_interior :
      ∀ c : ExplicitFormulaRectangleRegularGridCell F T ε, c ∈ cells →
        ∀ z : ℂ,
          z ∈ Set.Ioo (min c.lower.re c.upper.re)
                (max c.lower.re c.upper.re) ×ℂ
              Set.Ioo (min c.lower.im c.upper.im)
                (max c.lower.im c.upper.im) →
            z ∈ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_interiorOrBoundaryClosedSubdivision
    cells
    (fun c : ExplicitFormulaRectangleRegularGridCell F T ε => c.lower)
    (fun c : ExplicitFormulaRectangleRegularGridCell F T ε => c.upper)
    f F h hT hinterior hboundary hsubdivision hcell_location
    (fun c _hc z hz _hzInterior =>
      c.closedCell_not_mem_rawSingularCoordinates hz)
    hcell_open_interior
    (fun c _hc z hz =>
      c.openCell_not_mem_rawSingularCoordinates hz)

/-- Cauchy-Goursat zero for an inscribed-square-punctured rectangle from a finite family
of concrete regular grid cells.  The remaining geometric input is exactly the boundary
subdivision equality and the proof that each selected regular grid cell lies in the
contour interior. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridCells
    (cells : Finset ExplicitFormulaRectangleGridCellIndex)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleGridCellLower c)
            (explicitFormulaRectangleGridCellUpper c))
    (hcell_interior :
      ∀ c : ExplicitFormulaRectangleGridCellIndex,
        c ∈ cells →
          ∀ z : ℂ,
            z ∈
              ([[ (explicitFormulaRectangleGridCellLower c).re,
                (explicitFormulaRectangleGridCellUpper c).re ]] ×ℂ
                  [[ (explicitFormulaRectangleGridCellLower c).im,
                    (explicitFormulaRectangleGridCellUpper c).im ]]) →
              z ∈ explicitFormulaContourFamilyInterior F T)
    (hregular :
      ∀ c : ExplicitFormulaRectangleGridCellIndex,
        c ∈ cells →
          explicitFormulaRectangleGridCellRegularComplement F T ε c) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_interiorOffRawSingularClosedSubdivision
    cells
    explicitFormulaRectangleGridCellLower
    explicitFormulaRectangleGridCellUpper
    f F h hT hinterior hsubdivision hcell_interior
    (fun c hc z hz =>
      explicitFormulaRectangleGridCellRegularComplement_not_mem_rawSingularCoordinates
        F T ε c (hregular c hc) hz)

/-- The raw deleted-square boundary unfolds to the standard square boundary of the raw
completed explicit-formula integrand. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundary_eq
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawDeletedSquareBoundary f ε a =
      finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a ε := by
  rfl

/-- The raw deleted-square boundary is the subdivision-cell boundary of its
standard square lower-left and upper-right corners. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundary_eq_cellBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawDeletedSquareBoundary f ε a =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (finiteRectangleSquareLowerCorner a ε)
        (finiteRectangleSquareUpperCorner a ε) := by
  calc
    explicitFormulaRectangleRawDeletedSquareBoundary f ε a =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a ε := by
      exact explicitFormulaRectangleRawDeletedSquareBoundary_eq f ε a
    _ =
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (finiteRectangleSquareLowerCorner a ε)
          (finiteRectangleSquareUpperCorner a ε) := by
      exact
        finiteRectangleSquareBoundaryIntegral_eq_cellBoundary
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a ε

/-- The raw inscribed-square boundary unfolds to the standard square boundary of half-width
`ε / 2` for the raw completed explicit-formula integrand. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_eq
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareBoundary f ε a =
      finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a (ε / 2) := by
  rfl

/-- The raw inscribed-square boundary is the subdivision-cell boundary of its named
lower-left and upper-right corners. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_eq_cellBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareBoundary f ε a =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  rfl

/-- The raw inscribed-square boundary is the subdivision-cell boundary of the ordinary
deleted square at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_eq_deletedSquareCellBoundary_half
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareBoundary f ε a =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (finiteRectangleSquareLowerCorner a (ε / 2))
        (finiteRectangleSquareUpperCorner a (ε / 2)) := by
  calc
    explicitFormulaRectangleRawInscribedSquareBoundary f ε a =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a (ε / 2) := by
      exact explicitFormulaRectangleRawInscribedSquareBoundary_eq f ε a
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (finiteRectangleSquareLowerCorner a (ε / 2))
        (finiteRectangleSquareUpperCorner a (ε / 2)) := by
      exact
        finiteRectangleSquareBoundaryIntegral_eq_cellBoundary
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a (ε / 2)

/-- The half-width deleted-square boundary is the subdivision-cell boundary of the named
raw inscribed-square corners. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundary_half_eq_rawInscribedSquareCellBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2) a =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  calc
    explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2) a =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a (ε / 2) := by
      exact
        explicitFormulaRectangleRawDeletedSquareBoundary_eq f (ε / 2) a
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (finiteRectangleSquareLowerCorner a (ε / 2))
        (finiteRectangleSquareUpperCorner a (ε / 2)) := by
      exact
        finiteRectangleSquareBoundaryIntegral_eq_cellBoundary
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a (ε / 2)
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      rfl

/-- The inscribed-square boundary at circular radius `ε` is the deleted-square boundary
whose square half-width is `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_eq_rawDeletedSquareBoundary_half
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareBoundary f ε a =
      explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2) a := by
  rfl

/-- The deleted-square boundary at half-width `ε / 2` is the inscribed-square boundary at
circular radius `ε`. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundary_half_eq_rawInscribedSquareBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2) a =
      explicitFormulaRectangleRawInscribedSquareBoundary f ε a := by
  exact
    (explicitFormulaRectangleRawInscribedSquareBoundary_eq_rawDeletedSquareBoundary_half
      f ε a).symm

/-- The quarter-width deleted-square value required by the endpoint-data construction is
obtained from the corresponding half-radius inscribed-square value. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundary_quarter_eq_value_of_rawInscribedSquareBoundary_half_eq_value
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a value : ℂ)
    (hsquare :
      explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a = value) :
    explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value :=
  Eq.trans
    (explicitFormulaRectangleRawDeletedSquareBoundary_half_eq_rawInscribedSquareBoundary
      f (ε / 2) a)
    hsquare

/-- Finite-carrier construction of the downstream `hsquare` input from proved
half-radius inscribed-square values on every raw singular coordinate. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundary_quarter_eq_value_on_of_rawInscribedSquareBoundary_half_eq_value_on
    (f : ZetaAdmissibleFunction) (T ε : ℝ) (value : ℂ → ℂ)
    (hsquare :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a = value a) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value a :=
  fun a ha =>
    explicitFormulaRectangleRawDeletedSquareBoundary_quarter_eq_value_of_rawInscribedSquareBoundary_half_eq_value
      f ε a (value a) (hsquare a ha)

/-- Exact downstream `hsquare` construction from half-radius inscribed-square values
produced at each selected closed-radius scale. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundary_quarter_eq_value_of_rawInscribedSquareBoundary_half_eq_value_controls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (value : ℝ → ℂ → ℂ)
    (hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a = value ε a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a =
                value ε a := by
  intro ε hε hclosed hsep a ha
  exact
    explicitFormulaRectangleRawDeletedSquareBoundary_quarter_eq_value_of_rawInscribedSquareBoundary_half_eq_value
      f ε a (value ε a)
      (hsquare ε hε hclosed hsep a ha)

/-- Pointwise assembly of an inscribed-square boundary value from the centered inverse
square boundary theorem.  The remaining analytic input is exactly the local coefficient
reduction of the explicit-formula integrand to the inverse kernel on this square. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_half_eq_value_of_squareInverseBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a residue value : ℂ)
    (hprincipal :
      explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => (z - a)⁻¹) a ((ε / 2) / 2) • residue)
    (hinv :
      finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => (z - a)⁻¹) a ((ε / 2) / 2) =
          (2 * ↑Real.pi * Complex.I : ℂ))
    (hvalue :
      value = (2 * ↑Real.pi * Complex.I : ℂ) • residue) :
    explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a = value := by
  calc
    explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => (z - a)⁻¹) a ((ε / 2) / 2) • residue := by
      exact hprincipal
    _ = (2 * ↑Real.pi * Complex.I : ℂ) • residue := by
      exact congrArg (fun z : ℂ => z • residue) hinv
    _ = value := by
      exact hvalue.symm

/-- Pointwise assembly of an inscribed-square boundary value from the four inverse-kernel
side evaluations. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_half_eq_value_of_squareInverseSideValues
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a residue value : ℂ)
    (hprincipal :
      explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => (z - a)⁻¹) a ((ε / 2) / 2) • residue)
    (hbottom :
      finiteRectangleSquareSubInvBottomIntegral a ((ε / 2) / 2) =
        (Real.pi / 2 : ℂ) * Complex.I)
    (htop :
      finiteRectangleSquareSubInvTopIntegral a ((ε / 2) / 2) =
        -(Real.pi / 2 : ℂ) * Complex.I)
    (hright :
      Complex.I • finiteRectangleSquareSubInvRightIntegral a ((ε / 2) / 2) =
        (Real.pi / 2 : ℂ) * Complex.I)
    (hleft :
      Complex.I • finiteRectangleSquareSubInvLeftIntegral a ((ε / 2) / 2) =
        -(Real.pi / 2 : ℂ) * Complex.I)
    (hvalue :
      value = (2 * ↑Real.pi * Complex.I : ℂ) • residue) :
    explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a = value :=
  explicitFormulaRectangleRawInscribedSquareBoundary_half_eq_value_of_squareInverseBoundary
    f ε a residue value hprincipal
    (finiteRectangleSquareBoundaryIntegral_sub_inv_eq_twoPiI_of_sideValues
      a ((ε / 2) / 2) hbottom htop hright hleft)
    hvalue

/-- Finite-carrier construction of the downstream inscribed-square common-value
hypothesis from pointwise square inverse-boundary reductions. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_half_eq_commonValue_on_rawSingularCoordinates_of_squareInverseBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) (value residue : ℝ → ℂ → ℂ)
    (hprincipal :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
                  finiteRectangleSquareBoundaryIntegral
                    (fun z : ℂ => (z - a)⁻¹) a ((ε / 2) / 2) • residue ε a)
    (hinv :
      ∀ ε : ℝ,
        0 < ε →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              finiteRectangleSquareBoundaryIntegral
                (fun z : ℂ => (z - a)⁻¹) a ((ε / 2) / 2) =
                  (2 * ↑Real.pi * Complex.I : ℂ))
    (hvalue :
      ∀ ε : ℝ,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            value ε a = (2 * ↑Real.pi * Complex.I : ℂ) • residue ε a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
                value ε a := by
  intro ε hε hclosed hsep a ha
  exact
    explicitFormulaRectangleRawInscribedSquareBoundary_half_eq_value_of_squareInverseBoundary
      f ε a (residue ε a) (value ε a)
      (hprincipal ε hε hclosed hsep a ha)
      (hinv ε hε a ha)
      (hvalue ε a ha)

/-- Finite-carrier construction of the downstream inscribed-square common-value
hypothesis directly from four side evaluations of the centered inverse kernel. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundary_half_eq_commonValue_on_rawSingularCoordinates_of_squareInverseSideValues
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) (value residue : ℝ → ℂ → ℂ)
    (hprincipal :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
                  finiteRectangleSquareBoundaryIntegral
                    (fun z : ℂ => (z - a)⁻¹) a ((ε / 2) / 2) • residue ε a)
    (hbottom :
      ∀ ε : ℝ,
        0 < ε →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              finiteRectangleSquareSubInvBottomIntegral a ((ε / 2) / 2) =
                (Real.pi / 2 : ℂ) * Complex.I)
    (htop :
      ∀ ε : ℝ,
        0 < ε →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              finiteRectangleSquareSubInvTopIntegral a ((ε / 2) / 2) =
                -(Real.pi / 2 : ℂ) * Complex.I)
    (hright :
      ∀ ε : ℝ,
        0 < ε →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Complex.I • finiteRectangleSquareSubInvRightIntegral a ((ε / 2) / 2) =
                (Real.pi / 2 : ℂ) * Complex.I)
    (hleft :
      ∀ ε : ℝ,
        0 < ε →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a ((ε / 2) / 2) =
                -(Real.pi / 2 : ℂ) * Complex.I)
    (hvalue :
      ∀ ε : ℝ,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            value ε a = (2 * ↑Real.pi * Complex.I : ℂ) • residue ε a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
                value ε a := by
  intro ε hε hclosed hsep a ha
  exact
    explicitFormulaRectangleRawInscribedSquareBoundary_half_eq_value_of_squareInverseSideValues
      f ε a (residue ε a) (value ε a)
      (hprincipal ε hε hclosed hsep a ha)
      (hbottom ε hε a ha)
      (htop ε hε a ha)
      (hright ε hε a ha)
      (hleft ε hε a ha)
      (hvalue ε a ha)

/-- To prove the half-radius circle-to-inscribed-square transport, it is enough to deform
the half-radius circle to the deleted square whose half-width is half of that radius. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_of_rawDeletedSquare_quarter
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ)
    (hcircle_square :
      explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
        explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a) :
    explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
      explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a :=
  Eq.trans hcircle_square
    (explicitFormulaRectangleRawDeletedSquareBoundary_half_eq_rawInscribedSquareBoundary
      f (ε / 2) a)

/-- Finite-carrier form of the half-radius circle-to-inscribed-square transport: the only
geometric input still needed pointwise is deformation of each half-radius circle to the
deleted square whose half-width is half of that radius. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_rawDeletedSquare_quarter_on
    (f : ZetaAdmissibleFunction) (T ε : ℝ)
    (hcircle_square :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
            explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
          explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a :=
  fun a ha =>
    explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_of_rawDeletedSquare_quarter
      f ε a (hcircle_square a ha)

/-- A deleted-circle value and a deleted-square value with the same residue normalization
are equal.  This is the algebraic handoff for the missing geometric/residue primitive:
the analytic work is precisely to evaluate the square boundary with the same residue
value already used for the circle boundary. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_eq_rawDeletedSquareBoundary_of_common_value
    (f : ZetaAdmissibleFunction) (r R : ℝ) (a value : ℂ)
    (hcircle :
      explicitFormulaRectangleRawDeletedCircleBoundary f r a = value)
    (hsquare :
      explicitFormulaRectangleRawDeletedSquareBoundary f R a = value) :
    explicitFormulaRectangleRawDeletedCircleBoundary f r a =
      explicitFormulaRectangleRawDeletedSquareBoundary f R a :=
  Eq.trans hcircle hsquare.symm

/-- Corrected half-radius circle-to-quarter-square transport from common residue values.
The square half-width is `((ε / 2) / 2)`, matching the definition of
`explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2)`. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawDeletedSquareBoundary_quarter_of_common_value
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a value : ℂ)
    (hcircle :
      explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value)
    (hsquare :
      explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value) :
    explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
      explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a :=
  explicitFormulaRectangleRawDeletedCircleBoundary_eq_rawDeletedSquareBoundary_of_common_value
    f (ε / 2) ((ε / 2) / 2) a value hcircle hsquare

/-- Corrected half-radius circle-to-inscribed-square transport from common residue values. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_of_common_value
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a value : ℂ)
    (hcircle :
      explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value)
    (hsquare :
      explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value) :
    explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
      explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a :=
  explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_of_rawDeletedSquare_quarter
    f ε a
    (explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawDeletedSquareBoundary_quarter_of_common_value
      f ε a value hcircle hsquare)

/-- Finite-carrier pointwise circle-to-inscribed-square transport from common residue
values for the half-radius circle and the corresponding quarter-width deleted square. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_common_values
    (f : ZetaAdmissibleFunction) (T ε : ℝ) (value : ℂ → ℂ)
    (hcircle :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value a)
    (hsquare :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value a) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
          explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a :=
  fun a ha =>
    explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_of_common_value
      f ε a (value a) (hcircle a ha) (hsquare a ha)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
