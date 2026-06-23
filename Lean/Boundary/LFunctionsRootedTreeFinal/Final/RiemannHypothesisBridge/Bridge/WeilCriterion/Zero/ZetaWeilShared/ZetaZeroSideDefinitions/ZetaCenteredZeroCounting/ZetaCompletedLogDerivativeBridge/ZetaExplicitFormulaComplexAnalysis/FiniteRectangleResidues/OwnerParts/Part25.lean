import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part24

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

/-- The raw deleted-square boundary sum at half-width `ε / 2` is the raw
inscribed-square boundary sum at circular radius `ε`. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundarySum_half_eq_rawInscribedSquareBoundarySum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawDeletedSquareBoundarySum f T (ε / 2) =
      explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
  calc
    explicitFormulaRectangleRawDeletedSquareBoundarySum f T (ε / 2) =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2)) := by
      rfl
    _ =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawInscribedSquareBoundary f ε) := by
      exact Finset.sum_congr rfl
        (fun a _ha =>
          explicitFormulaRectangleRawDeletedSquareBoundary_half_eq_rawInscribedSquareBoundary
            f ε a)
    _ = explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
      rfl

/-- The raw inscribed-square boundary sum at circular radius `ε` is the raw
deleted-square boundary sum at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundarySum_eq_rawDeletedSquareBoundarySum_half
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε =
      explicitFormulaRectangleRawDeletedSquareBoundarySum f T (ε / 2) := by
  exact
    (explicitFormulaRectangleRawDeletedSquareBoundarySum_half_eq_rawInscribedSquareBoundarySum
      f T ε).symm

/-- The finite raw inscribed-square boundary sum is the finite carrier sum of the raw
inscribed-square boundary function. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundarySum_eq
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε =
      finiteRectangleDeletedCircleBoundarySum
        (explicitFormulaRectangleRawSingularCoordinates T)
        (explicitFormulaRectangleRawInscribedSquareBoundary f ε) := by
  rfl

/-- The finite raw inscribed-square boundary sum is the finite sum of the corresponding
subdivision-cell boundaries over the raw singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawInscribedSquareBoundarySum_eq_cellBoundarySum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  calc
    explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawInscribedSquareBoundary f ε) := by
      rfl
    _ =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact Finset.sum_congr rfl
        (fun a _ha =>
          explicitFormulaRectangleRawInscribedSquareBoundary_eq_cellBoundary f ε a)

/-- The oriented boundary integral of a finite punctured rectangle in the residue
normalization used in this owner file.  The outer rectangle is counterclockwise; each
deleted circle is recorded with positive residue orientation and therefore subtracted from
the punctured-domain boundary. -/
noncomputable def finiteRectanglePuncturedBoundaryIntegral
    (S : Finset ℂ) (outer : ℂ) (deletedCircle : ℂ → ℂ) : ℂ :=
  outer - finiteRectangleDeletedCircleBoundarySum S deletedCircle

/-- The finite punctured-rectangle boundary decomposes into the outer boundary minus the
positively oriented deleted-circle boundary sum. -/
theorem finiteRectanglePuncturedBoundaryIntegral_eq_outer_sub_deletedCircleBoundarySum
    (S : Finset ℂ) (outer : ℂ) (deletedCircle : ℂ → ℂ) :
    finiteRectanglePuncturedBoundaryIntegral S outer deletedCircle =
      outer - finiteRectangleDeletedCircleBoundarySum S deletedCircle := by
  rfl

/-- If two deleted-boundary choices have the same finite deleted-boundary sum, then
vanishing of the punctured-boundary integral for one choice transports to the other. -/
theorem finiteRectanglePuncturedBoundaryIntegral_eq_zero_of_deletedBoundarySum_eq
    (S : Finset ℂ) (outer : ℂ) (deletedBoundary₁ deletedBoundary₂ : ℂ → ℂ)
    (hzero :
      finiteRectanglePuncturedBoundaryIntegral S outer deletedBoundary₂ = 0)
    (hsum :
      finiteRectangleDeletedCircleBoundarySum S deletedBoundary₁ =
        finiteRectangleDeletedCircleBoundarySum S deletedBoundary₂) :
    finiteRectanglePuncturedBoundaryIntegral S outer deletedBoundary₁ = 0 := by
  calc
    finiteRectanglePuncturedBoundaryIntegral S outer deletedBoundary₁ =
        outer - finiteRectangleDeletedCircleBoundarySum S deletedBoundary₁ := by
      exact
        finiteRectanglePuncturedBoundaryIntegral_eq_outer_sub_deletedCircleBoundarySum
          S outer deletedBoundary₁
    _ = outer - finiteRectangleDeletedCircleBoundarySum S deletedBoundary₂ := by
      exact congrArg (fun x : ℂ => outer - x) hsum
    _ = finiteRectanglePuncturedBoundaryIntegral S outer deletedBoundary₂ := by
      exact
        (finiteRectanglePuncturedBoundaryIntegral_eq_outer_sub_deletedCircleBoundarySum
          S outer deletedBoundary₂).symm
    _ = 0 := by
      exact hzero

/-- Pointwise equality of two deleted-boundary choices on the finite carrier gives equality
of their finite deleted-boundary sums. -/
theorem finiteRectangleDeletedCircleBoundarySum_eq_of_forall_mem
    (S : Finset ℂ) (deletedBoundary₁ deletedBoundary₂ : ℂ → ℂ)
    (hpoint :
      ∀ a : ℂ, a ∈ S → deletedBoundary₁ a = deletedBoundary₂ a) :
    finiteRectangleDeletedCircleBoundarySum S deletedBoundary₁ =
      finiteRectangleDeletedCircleBoundarySum S deletedBoundary₂ := by
  exact Finset.sum_congr rfl hpoint

/-- Pointwise circle-to-inscribed-square deleted-boundary transport gives equality of the
finite deleted-boundary sums over the raw singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_rawInscribedSquareBoundarySum_of_boundary_eq_on
    (f : ZetaAdmissibleFunction) (T ε : ℝ)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f ε a =
            explicitFormulaRectangleRawInscribedSquareBoundary f ε a) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
      explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
  calc
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedCircleBoundary f ε) := by
      rfl
    _ =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawInscribedSquareBoundary f ε) := by
      exact
        finiteRectangleDeletedCircleBoundarySum_eq_of_forall_mem
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedCircleBoundary f ε)
          (explicitFormulaRectangleRawInscribedSquareBoundary f ε)
          hdeleted
    _ = explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
      rfl

/-- Finite-sum form of the corrected half-radius circle-to-inscribed-square transport.
The geometric input is the pointwise deformation from the half-radius circle to the
quarter-width deleted square. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_half_eq_rawInscribedSquareBoundarySum_half_of_rawDeletedSquare_quarter_on
    (f : ZetaAdmissibleFunction) (T ε : ℝ)
    (hcircle_square :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
            explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T (ε / 2) =
      explicitFormulaRectangleRawInscribedSquareBoundarySum f T (ε / 2) :=
  explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_rawInscribedSquareBoundarySum_of_boundary_eq_on
    f T (ε / 2)
    (explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_rawDeletedSquare_quarter_on
      f T ε hcircle_square)

/-- Finite-carrier half-radius circle-to-inscribed-square transport from common residue
values at each raw singular coordinate. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_half_eq_rawInscribedSquareBoundarySum_half_of_common_values
    (f : ZetaAdmissibleFunction) (T ε : ℝ) (value : ℂ → ℂ)
    (hcircle :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value a)
    (hsquare :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value a) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T (ε / 2) =
      explicitFormulaRectangleRawInscribedSquareBoundarySum f T (ε / 2) :=
  explicitFormulaRectangleRawDeletedCircleBoundarySum_half_eq_rawInscribedSquareBoundarySum_half_of_rawDeletedSquare_quarter_on
    f T ε
    (fun a ha =>
      explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawDeletedSquareBoundary_quarter_of_common_value
        f ε a (value a) (hcircle a ha) (hsquare a ha))

/-- Pointwise circle-to-deleted-square deleted-boundary transport gives equality of the
finite deleted-boundary sums over the raw singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_rawDeletedSquareBoundarySum_of_boundary_eq_on
    (f : ZetaAdmissibleFunction) (T ε : ℝ)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f ε a =
            explicitFormulaRectangleRawDeletedSquareBoundary f ε a) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
      explicitFormulaRectangleRawDeletedSquareBoundarySum f T ε := by
  calc
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedCircleBoundary f ε) := by
      rfl
    _ =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedSquareBoundary f ε) := by
      exact
        finiteRectangleDeletedCircleBoundarySum_eq_of_forall_mem
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedCircleBoundary f ε)
          (explicitFormulaRectangleRawDeletedSquareBoundary f ε)
          hdeleted
    _ = explicitFormulaRectangleRawDeletedSquareBoundarySum f T ε := by
      rfl

/-- Pointwise circle-to-half-width deleted-square transport identifies the raw
deleted-circle boundary sum with the inscribed-square boundary sum. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_rawInscribedSquareBoundarySum_of_halfDeletedSquare_eq_on
    (f : ZetaAdmissibleFunction) (T ε : ℝ)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
            explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2) a) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T (ε / 2) =
      explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
  calc
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T (ε / 2) =
        explicitFormulaRectangleRawDeletedSquareBoundarySum f T (ε / 2) := by
      exact
        explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_rawDeletedSquareBoundarySum_of_boundary_eq_on
          f T (ε / 2) hdeleted
    _ = explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
      exact
        explicitFormulaRectangleRawDeletedSquareBoundarySum_half_eq_rawInscribedSquareBoundarySum
          f T ε

/-- Finite raw deleted-circle boundary sums are unchanged when every raw deleted circle is
transported through a regular annulus from radius `R` down to radius `r`. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_of_annulus_regular
    (f : ZetaAdmissibleFunction) (T : ℝ) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (s : ℂ → Set ℂ)
    (hs : ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T → (s a).Countable)
    (hcontinuous :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ContinuousOn
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall a R \ Metric.ball a r))
    (hdifferentiable :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ z : ℂ,
            z ∈ (Metric.ball a R \ Metric.closedBall a r) \ s a →
              DifferentiableAt ℂ
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T R =
      explicitFormulaRectangleRawDeletedCircleBoundarySum f T r :=
  finiteRectangleDeletedCircleBoundarySum_eq_of_forall_mem
    (explicitFormulaRectangleRawSingularCoordinates T)
    (explicitFormulaRectangleRawDeletedCircleBoundary f R)
    (explicitFormulaRectangleRawDeletedCircleBoundary f r)
    (fun a ha =>
      explicitFormulaRectangleRawDeletedCircleBoundary_eq_of_annulus_regular
        f hr hrR (s a) (hs a ha)
        (hcontinuous a ha)
        (hdifferentiable a ha))

/-- If two deleted-boundary choices agree pointwise on the finite carrier, then vanishing
of one punctured-boundary integral transports to the other. -/
theorem finiteRectanglePuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
    (S : Finset ℂ) (outer : ℂ) (deletedBoundary₁ deletedBoundary₂ : ℂ → ℂ)
    (hzero :
      finiteRectanglePuncturedBoundaryIntegral S outer deletedBoundary₂ = 0)
    (hpoint :
      ∀ a : ℂ, a ∈ S → deletedBoundary₁ a = deletedBoundary₂ a) :
    finiteRectanglePuncturedBoundaryIntegral S outer deletedBoundary₁ = 0 :=
  finiteRectanglePuncturedBoundaryIntegral_eq_zero_of_deletedBoundarySum_eq
    S outer deletedBoundary₁ deletedBoundary₂ hzero
    (finiteRectangleDeletedCircleBoundarySum_eq_of_forall_mem
      S deletedBoundary₁ deletedBoundary₂ hpoint)

/-- Boundary accounting for the punctured rectangle orientation: if Cauchy-Goursat gives
zero on the punctured boundary, and the punctured boundary decomposes as outer boundary
minus the positively oriented deleted-circle contributions, then the outer boundary equals
the finite deleted-circle sum. -/
theorem finiteRectangle_outerBoundary_eq_deletedCircleBoundarySum_of_puncturedBoundary
    (S : Finset ℂ) (outer : ℂ) (deletedCircle : ℂ → ℂ)
    (puncturedBoundary : ℂ)
    (hdecomp :
      puncturedBoundary =
        outer - finiteRectangleDeletedCircleBoundarySum S deletedCircle)
    (hcauchy : puncturedBoundary = 0) :
    outer = finiteRectangleDeletedCircleBoundarySum S deletedCircle := by
  let D : ℂ := finiteRectangleDeletedCircleBoundarySum S deletedCircle
  have houter_sub : outer - D = 0 := by
    calc
      outer - D = puncturedBoundary := by
        exact hdecomp.symm
      _ = 0 := by
        exact hcauchy
  calc
    outer = (outer - D) + D := by
      exact (sub_add_cancel outer D).symm
    _ = 0 + D := by
      exact congrArg (fun z : ℂ => z + D) houter_sub
    _ = D := by
      exact zero_add D

/-- If the finite punctured rectangle has zero boundary integral by Cauchy-Goursat, then
the outer rectangle boundary equals the positively oriented finite deleted-circle boundary
sum. -/
theorem finiteRectangle_outerBoundary_eq_deletedCircleBoundarySum_of_puncturedBoundaryIntegral_zero
    (S : Finset ℂ) (outer : ℂ) (deletedCircle : ℂ → ℂ)
    (hcauchy :
      finiteRectanglePuncturedBoundaryIntegral S outer deletedCircle = 0) :
    outer = finiteRectangleDeletedCircleBoundarySum S deletedCircle := by
  exact
    finiteRectangle_outerBoundary_eq_deletedCircleBoundarySum_of_puncturedBoundary
      S outer deletedCircle
      (finiteRectanglePuncturedBoundaryIntegral S outer deletedCircle)
      (finiteRectanglePuncturedBoundaryIntegral_eq_outer_sub_deletedCircleBoundarySum
        S outer deletedCircle)
      hcauchy

/-- The finite punctured-boundary integral for the completed explicit-formula rectangle,
with the project rectangle contour integral as the outer boundary term. -/
noncomputable def explicitFormulaRectanglePuncturedBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ) : ℂ :=
  finiteRectanglePuncturedBoundaryIntegral S
    (zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T))
    deletedCircle

/-- The completed explicit-formula punctured-boundary integral unfolds to the project
outer rectangle contour integral minus the finite deleted-circle boundary sum. -/
theorem explicitFormulaRectanglePuncturedBoundaryIntegral_eq_contour_sub_deletedCircleBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ) :
    explicitFormulaRectanglePuncturedBoundaryIntegral f F T S deletedCircle =
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
        finiteRectangleDeletedCircleBoundarySum S deletedCircle := by
  rfl

/-- If the completed explicit-formula finite punctured rectangle has zero boundary
integral, then the project outer rectangle contour equals the finite deleted-circle
boundary sum in positive residue orientation. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_deletedCircleBoundarySum_of_puncturedBoundaryIntegral_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ)
    (hcauchy :
      explicitFormulaRectanglePuncturedBoundaryIntegral f F T S deletedCircle = 0) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      finiteRectangleDeletedCircleBoundarySum S deletedCircle := by
  exact
    finiteRectangle_outerBoundary_eq_deletedCircleBoundarySum_of_puncturedBoundaryIntegral_zero
      S
      (zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T))
      deletedCircle
      hcauchy

/-- The punctured-boundary integral for the completed explicit-formula rectangle in the
tangent-weighted contour normalization used by Cauchy-Goursat. -/
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

/-- The tangent punctured-boundary integral unfolds to the tangent outer rectangle contour
minus the finite deleted-circle boundary sum. -/
theorem explicitFormulaRectangleTangentPuncturedBoundaryIntegral_eq_tangentContour_sub_deletedCircleBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ) :
    explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T S deletedCircle =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        finiteRectangleDeletedCircleBoundarySum S deletedCircle := by
  rfl

/-- The finite-radius tangent punctured-boundary integral unfolds to the tangent outer
rectangle contour minus the actual raw deleted-circle boundary sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_tangentContour_sub_rawDeletedCircleBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε := by
  rfl

/-- The finite-radius tangent square-punctured boundary unfolds to the tangent outer
rectangle contour minus the raw deleted-square boundary sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawDeletedSquareBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawDeletedSquareBoundarySum f T ε := by
  rfl

/-- The finite-radius tangent square-punctured boundary unfolds to the tangent
outer rectangle contour minus the finite sum of the corresponding raw deleted-square
cell boundaries. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawDeletedSquareCellBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (finiteRectangleSquareLowerCorner a ε)
            (finiteRectangleSquareUpperCorner a ε) := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawDeletedSquareBoundarySum f T ε := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawDeletedSquareBoundarySum
          f F T ε
    _ =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (finiteRectangleSquareLowerCorner a ε)
            (finiteRectangleSquareUpperCorner a ε) := by
      exact congrArg
        (fun x : ℂ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) - x)
        (explicitFormulaRectangleRawDeletedSquareBoundarySum_eq_cellBoundarySum f T ε)

/-- The finite-radius tangent inscribed-square-punctured boundary unfolds to the tangent
outer rectangle contour minus the raw inscribed-square boundary sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawInscribedSquareBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
  rfl

/-- A square-punctured boundary at square half-width `ε / 2` is the same finite boundary
expression as the inscribed-square-punctured boundary at circular radius `ε`. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_half_eq_inscribedSquarePuncturedBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) =
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawDeletedSquareBoundarySum f T (ε / 2) := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawDeletedSquareBoundarySum
          f F T (ε / 2)
    _ =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
      exact congrArg
        (fun x : ℂ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) - x)
        (explicitFormulaRectangleRawDeletedSquareBoundarySum_half_eq_rawInscribedSquareBoundarySum
          f T ε)
    _ =
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε := by
      exact
        (explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawInscribedSquareBoundarySum
          f F T ε).symm

/-- The inscribed-square-punctured boundary at circular radius `ε` is the same finite
boundary expression as the square-punctured boundary at square half-width `ε / 2`. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_squarePuncturedBoundary_half
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) := by
  exact
    (explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_half_eq_inscribedSquarePuncturedBoundary
      f F T ε).symm

/-- Zero of the square-punctured boundary at square half-width `ε / 2` transports to the
inscribed-square-punctured boundary at circular radius `ε`. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_squareHalfPuncturedBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsquare :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) = 0) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_squarePuncturedBoundary_half
          f F T ε
    _ = 0 := by
      exact hsquare

/-- Zero of the inscribed-square-punctured boundary at circular radius `ε` transports to
the square-punctured boundary at square half-width `ε / 2`. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_half_eq_zero_of_inscribedSquarePuncturedBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hinscribed :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε = 0) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
      f F T (ε / 2) = 0 := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) =
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_half_eq_inscribedSquarePuncturedBoundary
          f F T ε
    _ = 0 := by
      exact hinscribed

/-- The finite-radius tangent inscribed-square punctured boundary unfolds to the tangent
outer rectangle contour minus the finite sum of the corresponding inscribed-square
subdivision-cell boundaries. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawInscribedSquareCellBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawInscribedSquareBoundarySum
          f F T ε
    _ =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact congrArg
        (fun x : ℂ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) - x)
        (explicitFormulaRectangleRawInscribedSquareBoundarySum_eq_cellBoundarySum f T ε)

/-- The half-width square-punctured boundary unfolds directly to the tangent outer
rectangle contour minus the finite inscribed-square cell-boundary sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_half_eq_tangentContour_sub_rawInscribedSquareCellBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) =
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_half_eq_inscribedSquarePuncturedBoundary
          f F T ε
    _ =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawInscribedSquareCellBoundarySum
          f F T ε

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
