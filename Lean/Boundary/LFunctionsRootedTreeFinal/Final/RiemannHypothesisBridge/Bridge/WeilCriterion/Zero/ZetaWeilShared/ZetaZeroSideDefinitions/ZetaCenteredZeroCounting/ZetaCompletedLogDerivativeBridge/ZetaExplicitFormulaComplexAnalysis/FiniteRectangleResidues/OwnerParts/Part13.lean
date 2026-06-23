import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part12

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

/-- Cauchy-Goursat zero for the finite-radius inscribed-square-punctured rectangle from a
concrete subdivision by regular rectangular cells contained in the raw punctured interior. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_rawPuncturedSubdivision
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
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
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
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 := by
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
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_cellCauchy
      cells lower upper s f F T ε hsubdivision hs Hc Hd

/-- Cauchy-Goursat zero for the finite-radius inscribed-square-punctured rectangle from a
concrete subdivision by rectangular cells whose closed rectangles lie in the raw punctured
interior. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_rawPuncturedClosedSubdivision
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
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
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
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_rawPuncturedSubdivision
    cells lower upper f F h hT hε hinterior hsubdivision hcell_closed
    (fun c hc =>
      Set.Subset.trans
        (finiteRectangleSubdivisionOpenCell_subset_closedCell (lower c) (upper c))
        (hcell_closed c hc))

/-- Cauchy-Goursat zero for the finite-radius inscribed-square-punctured rectangle from a
concrete subdivision by rectangular cells whose closed rectangles lie in the contour
interior and avoid the raw finite singular-coordinate carrier.  This is the regularity
consumer suited to square-hole complement cells: the cells need not avoid the whole
radius-`ε` deleted balls. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_interiorOffRawSingularClosedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_interior :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T)
    (hcell_offRaw :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) →
            z ∉ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 := by
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
      explicitFormulaRectangleInteriorOffRawSingular_continuousOn
        f F h hT hinterior
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]])
        (hcell_interior c hc)
        (hcell_offRaw c hc)
  have Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x := by
    intro c hc x hx
    have hxClosed :
        x ∈ ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]]) :=
      finiteRectangleSubdivisionOpenCell_subset_closedCell
        (lower c) (upper c) hx.1
    exact
      explicitFormulaRectangleInteriorOffRawSingular_differentiableAt
        f F h hT hinterior
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]])
        (hcell_interior c hc)
        (hcell_offRaw c hc)
        hxClosed
  exact
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_cellCauchy
      cells lower upper s f F T ε hsubdivision hs Hc Hd

/-- Cauchy-Goursat zero for the finite-radius inscribed-square-punctured rectangle from a
subdivision whose closed cells may meet the outer contour boundary.  Boundary points supply
continuity through `hboundary`; differentiability is only used on open cells contained in
the contour interior and avoiding the raw singular carrier. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_interiorOrBoundaryClosedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T)
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
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_location :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T ∨
              z ∈ explicitFormulaContourFamilyBoundary F T)
    (hcell_closed_offRaw :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T →
              z ∉ explicitFormulaRectangleRawSingularCoordinates T)
    (hcell_open_interior :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ Set.Ioo (min (lower c).re (upper c).re)
                (max (lower c).re (upper c).re) ×ℂ
              Set.Ioo (min (lower c).im (upper c).im)
                (max (lower c).im (upper c).im) →
            z ∈ explicitFormulaContourFamilyInterior F T)
    (hcell_open_offRaw :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ Set.Ioo (min (lower c).re (upper c).re)
                (max (lower c).re (upper c).re) ×ℂ
              Set.Ioo (min (lower c).im (upper c).im)
                (max (lower c).im (upper c).im) →
            z ∉ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 := by
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
      explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousOn
        f F h hT hinterior hboundary
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]])
        (hcell_location c hc)
        (hcell_closed_offRaw c hc)
  have Hd :
      ∀ c : ι, c ∈ cells →
        ∀ x : ℂ,
          x ∈
              Set.Ioo (min (lower c).re (upper c).re)
                  (max (lower c).re (upper c).re) ×ℂ
                Set.Ioo (min (lower c).im (upper c).im)
                  (max (lower c).im (upper c).im) \ s c →
            DifferentiableAt ℂ
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x := by
    intro c hc x hx
    exact
      completedZetaContourIntegrand_differentiableAt_off_singularSet
        h.phi_control
        (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
          F hT hinterior
          (hcell_open_interior c hc x hx.1)
          (hcell_open_offRaw c hc x hx.1))
  exact
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_cellCauchy
      cells lower upper s f F T ε hsubdivision hs Hc Hd

/-- Cauchy-Goursat zero for an inscribed-square-punctured rectangle from complement cells:
each regular cell lies in the contour interior and is disjoint from every removed
inscribed-square closed cell.  The avoidance of raw singular coordinates is derived from
the fact that every raw singular center lies in its own removed square. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_inscribedSquareComplementClosedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 ≤ ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_interior :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T)
    (hcell_disjoint :
      ∀ c : ι, c ∈ cells →
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Disjoint
              ([[ (lower c).re, (upper c).re ]] ×ℂ
                [[ (lower c).im, (upper c).im ]])
              (explicitFormulaRectangleRawInscribedSquareClosedCell ε a)) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_interiorOffRawSingularClosedSubdivision
    cells lower upper f F h hT hinterior hsubdivision hcell_interior
    (fun c hc z hz =>
      explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_disjoint_inscribedSquares
        T ε hε (lower c) (upper c) (hcell_disjoint c hc) hz)

/-- Cauchy-Goursat zero for an inscribed-square-punctured rectangle from complement cells
whose coordinate intervals omit every raw singular center in at least one coordinate.  This
is the form naturally produced by a grid subdivision by the sides of the removed squares. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_coordinateOmittingClosedSubdivision
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_interior :
      ∀ c : ι, c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ (lower c).re, (upper c).re ]] ×ℂ
            [[ (lower c).im, (upper c).im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T)
    (hcell_omits_raw :
      ∀ c : ι, c ∈ cells →
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            a.re ∉ [[ (lower c).re, (upper c).re ]] ∨
              a.im ∉ [[ (lower c).im, (upper c).im ]]) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_interiorOffRawSingularClosedSubdivision
    cells lower upper f F h hT hinterior hsubdivision hcell_interior
    (fun c hc z hz =>
      explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_coordinate_omission
        T (lower c) (upper c) (hcell_omits_raw c hc) hz)

/-- A completed-zero local residue coefficient limit transports along any punctured
parametrization approaching that completed-zero coordinate.  This is the one-coordinate
input used for deleted-circle boundary limits in the punctured-rectangle construction. -/
theorem explicitFormulaRectangle_completedZero_localResidue_along_puncturedParam
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T)
    (γ : ι → ℂ)
    (hγ : Tendsto γ l (𝓝[≠] (completedZeroResidueCoordinate ρ)))
    (hlocal :
      ∀ σ : {σ : ℂ // ZetaCompletedZero σ},
        σ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate σ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate σ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero σ)))) :
    Tendsto
      (fun i : ι =>
        (γ i - completedZeroResidueCoordinate ρ) *
          zetaCompletedExplicitFormulaContourIntegrand f (γ i))
      l
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) := by
  exact
    (explicitFormulaRectangle_completedZeroWindow_coordinate_localResidue
      f T hlocal hρ).comp hγ

/-- The preceding one-coordinate transport specialized to a completed-zero coordinate
which has first been found as an interior non-pole singularity. -/
theorem explicitFormulaRectangle_nonPoleInteriorSingular_localResidue_along_puncturedParam
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinterior :
      ∀ σ : {σ : ℂ // ZetaCompletedZero σ},
        σ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate σ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate σ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hzInterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hzSingular : z ∈ completedZetaContourIntegrandSingularSet)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (γ : ι → ℂ)
    (hγ :
      Tendsto γ l
        (𝓝[≠]
          (completedZeroResidueCoordinate
            (explicitFormulaCompletedZeroOfContourZero z hz0 hz1
              (explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
                F T hzInterior hzSingular hz0 hz1)))))
    (hlocal :
      ∀ σ : {σ : ℂ // ZetaCompletedZero σ},
        σ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun w : ℂ =>
              (w - completedZeroResidueCoordinate σ) *
                zetaCompletedExplicitFormulaContourIntegrand f w)
            (𝓝[≠] (completedZeroResidueCoordinate σ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero σ)))) :
    Tendsto
      (fun i : ι =>
        (γ i -
            completedZeroResidueCoordinate
              (explicitFormulaCompletedZeroOfContourZero z hz0 hz1
                (explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
                  F T hzInterior hzSingular hz0 hz1))) *
          zetaCompletedExplicitFormulaContourIntegrand f (γ i))
      l
      (𝓝
        (explicitFormulaZeroResidue f
          (explicitFormulaZeroDataOfCompletedZero
            (explicitFormulaCompletedZeroOfContourZero z hz0 hz1
              (explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
                F T hzInterior hzSingular hz0 hz1))))) := by
  let hzeta : completedRiemannZeta z = 0 :=
    explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
      F T hzInterior hzSingular hz0 hz1
  let ρ : {ρ : ℂ // ZetaCompletedZero ρ} :=
    explicitFormulaCompletedZeroOfContourZero z hz0 hz1 hzeta
  have hρWindow : ρ ∈ explicitFormulaCompletedZeroHeightWindow T :=
    explicitFormulaRectangle_interiorSingular_nonPole_completedZero_mem_window
      F T hinterior hzInterior hzSingular hz0 hz1
  exact
    explicitFormulaRectangle_completedZero_localResidue_along_puncturedParam
      f T ρ hρWindow γ hγ hlocal

/-- One-coordinate deleted-circle residue theorem in Mathlib's circle normalization:
if the local coefficient tends to the residue at a puncture, then the Cauchy circle
integral of that coefficient has value `(2πi) • residue`. -/
theorem finiteRectangle_deletedCircleCoefficientIntegral_eq_twoPiI_smul_residue
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (coeff : ℂ → ℂ) (residue : ℂ) (s : Set ℂ)
    (hs : s.Countable)
    (hcontinuous : ContinuousOn coeff (Metric.closedBall c R \ {c}))
    (hdifferentiable :
      ∀ z : ℂ, z ∈ (Metric.ball c R \ {c}) \ s →
        DifferentiableAt ℂ coeff z)
    (hlocal : Tendsto coeff (𝓝[≠] c) (𝓝 residue)) :
    (∮ z in C(c, R), (z - c)⁻¹ • coeff z) =
      (2 * ↑Real.pi * Complex.I : ℂ) • residue := by
  exact
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      hR hs hcontinuous hdifferentiable hlocal

/-- One-coordinate deleted-circle residue theorem for the actual meromorphic integrand in
Mathlib's circle normalization.

The local input is stated in coefficient form, `coeff z = (z - c) * g z`, so the result
is the raw circle integral of `g` and carries the unavoidable `2πi` factor. -/
theorem finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (g : ℂ → ℂ) (residue : ℂ) (s : Set ℂ)
    (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ => (z - c) * g z)
        (Metric.closedBall c R \ {c}))
    (hdifferentiable :
      ∀ z : ℂ, z ∈ (Metric.ball c R \ {c}) \ s →
        DifferentiableAt ℂ (fun w : ℂ => (w - c) * g w) z)
    (hlocal :
      Tendsto (fun z : ℂ => (z - c) * g z) (𝓝[≠] c) (𝓝 residue)) :
    (∮ z in C(c, R), g z) =
      (2 * ↑Real.pi * Complex.I : ℂ) • residue := by
  calc
    (∮ z in C(c, R), g z) =
        (∮ z in C(c, R), (z - c)⁻¹ • ((z - c) * g z)) := by
      exact
        (circleIntegral.integral_sub_inv_smul_sub_smul g c c R).symm
    _ = (2 * ↑Real.pi * Complex.I : ℂ) • residue := by
      exact
        finiteRectangle_deletedCircleCoefficientIntegral_eq_twoPiI_smul_residue
          hR
          (fun z : ℂ => (z - c) * g z)
          residue
          s
          hs
          hcontinuous
          hdifferentiable
          hlocal

/-- Deleted-circle boundary values are invariant under radial enlargement across a regular
annulus.  This is the local transport used when the finite-hole construction replaces one
deleted circle radius by another while staying away from the puncture. -/
theorem finiteRectangle_deletedCircleIntegral_eq_of_annulus_regular
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (g : ℂ → ℂ) (s : Set ℂ) (hs : s.Countable)
    (hcontinuous : ContinuousOn g (Metric.closedBall c R \ Metric.ball c r))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball c R \ Metric.closedBall c r) \ s →
          DifferentiableAt ℂ g z) :
    (∮ z in C(c, R), g z) = (∮ z in C(c, r), g z) :=
  Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR hs hcontinuous hdifferentiable

/-- Deleted-circle residue theorem at one completed-zero coordinate, in Mathlib's circle
normalization.  The coefficient is the punctured local residue coefficient
`(z - ρ_coord) * integrand z`; continuity and differentiability on the deleted disk are
the local regularity inputs supplied by the punctured-rectangle construction. -/
theorem explicitFormulaRectangle_completedZero_deletedCircleCoefficientIntegral_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ =>
          (z - completedZeroResidueCoordinate ρ) *
            zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (completedZeroResidueCoordinate ρ) R \
          {completedZeroResidueCoordinate ρ}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) R \
            {completedZeroResidueCoordinate ρ}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (w - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hlocal :
      ∀ σ : {σ : ℂ // ZetaCompletedZero σ},
        σ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate σ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate σ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero σ)))) :
    (∮ z in C(completedZeroResidueCoordinate ρ, R),
        (z - completedZeroResidueCoordinate ρ)⁻¹ •
          ((z - completedZeroResidueCoordinate ρ) *
            zetaCompletedExplicitFormulaContourIntegrand f z)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
  exact
    finiteRectangle_deletedCircleCoefficientIntegral_eq_twoPiI_smul_residue
      hR
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) *
          zetaCompletedExplicitFormulaContourIntegrand f z)
      (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
      s
      hs
      hcontinuous
      hdifferentiable
      (explicitFormulaRectangle_completedZeroWindow_coordinate_localResidue
        f T hlocal hρ)

/-- Deleted-circle residue theorem at one completed-zero coordinate for the actual
completed explicit-formula integrand in Mathlib's circle normalization. -/
theorem explicitFormulaRectangle_completedZero_deletedCircleIntegral_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ =>
          (z - completedZeroResidueCoordinate ρ) *
            zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (completedZeroResidueCoordinate ρ) R \
          {completedZeroResidueCoordinate ρ}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) R \
            {completedZeroResidueCoordinate ρ}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (w - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hlocal :
      ∀ σ : {σ : ℂ // ZetaCompletedZero σ},
        σ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate σ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate σ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero σ)))) :
    (∮ z in C(completedZeroResidueCoordinate ρ, R),
        zetaCompletedExplicitFormulaContourIntegrand f z) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
  exact
    finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue
      hR
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
      s
      hs
      hcontinuous
      hdifferentiable
      (explicitFormulaRectangle_completedZeroWindow_coordinate_localResidue
        f T hlocal hρ)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
