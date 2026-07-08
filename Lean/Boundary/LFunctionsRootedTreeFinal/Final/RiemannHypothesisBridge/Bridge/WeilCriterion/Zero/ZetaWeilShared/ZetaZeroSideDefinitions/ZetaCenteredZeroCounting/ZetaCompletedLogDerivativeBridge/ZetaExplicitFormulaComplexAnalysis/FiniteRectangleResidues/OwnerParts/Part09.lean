import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part08

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

/-- The completed contour integrand is differentiable at every point of any set contained
in the contour interior and disjoint from the raw finite singular-coordinate carrier. -/
theorem explicitFormulaRectangleInteriorOffRawSingular_differentiableAt
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (R : Set ℂ)
    (hRInterior :
      ∀ z : ℂ, z ∈ R → z ∈ explicitFormulaContourFamilyInterior F T)
    (hROff :
      ∀ z : ℂ, z ∈ R → z ∉ explicitFormulaRectangleRawSingularCoordinates T)
    {z : ℂ}
    (hz : z ∈ R) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_differentiableAt_off_singularSet
      h.phi_control
      (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
        F hT hinterior (hRInterior z hz) (hROff z hz))

/-- The completed contour integrand is continuous at every point of any set contained in
the contour interior and disjoint from the raw finite singular-coordinate carrier. -/
theorem explicitFormulaRectangleInteriorOffRawSingular_continuousAt
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (R : Set ℂ)
    (hRInterior :
      ∀ z : ℂ, z ∈ R → z ∈ explicitFormulaContourFamilyInterior F T)
    (hROff :
      ∀ z : ℂ, z ∈ R → z ∉ explicitFormulaRectangleRawSingularCoordinates T)
    {z : ℂ}
    (hz : z ∈ R) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_continuousAt_off_singularSet
      h.phi_control
      (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
        F hT hinterior (hRInterior z hz) (hROff z hz))

/-- The completed contour integrand is continuous on any set contained in the contour
interior and disjoint from the raw finite singular-coordinate carrier. -/
theorem explicitFormulaRectangleInteriorOffRawSingular_continuousOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (R : Set ℂ)
    (hRInterior :
      ∀ z : ℂ, z ∈ R → z ∈ explicitFormulaContourFamilyInterior F T)
    (hROff :
      ∀ z : ℂ, z ∈ R → z ∉ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) R :=
  fun _z hz =>
    (explicitFormulaRectangleInteriorOffRawSingular_continuousAt
      f F h hT hinterior R hRInterior hROff hz).continuousWithinAt

/-- The completed contour integrand is continuous at points of a set that lies in the
contour interior or on the contour boundary.  Interior points are handled by off-raw
regularity; boundary points use the explicit boundary-regularity input of the finite
Cauchy residue theorem. -/
theorem explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousAt
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
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
    (R : Set ℂ)
    (hRLocation :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T ∨
          z ∈ explicitFormulaContourFamilyBoundary F T)
    (hROff :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T →
          z ∉ explicitFormulaRectangleRawSingularCoordinates T)
    {z : ℂ}
    (hz : z ∈ R) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  match hRLocation z hz with
  | Or.inl hzInterior =>
      exact
        completedZetaContourIntegrand_continuousAt_off_singularSet
          h.phi_control
          (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
            F hT hinterior hzInterior (hROff z hz hzInterior))
  | Or.inr hzBoundary =>
      exact (hboundary z hzBoundary).1

/-- The completed contour integrand is continuous on any set lying in the contour interior
or on the contour boundary, provided interior points avoid the raw singular carrier. -/
theorem explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
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
    (R : Set ℂ)
    (hRLocation :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T ∨
          z ∈ explicitFormulaContourFamilyBoundary F T)
    (hROff :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T →
          z ∉ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) R :=
  fun _z hz =>
    (explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousAt
      f F h hT hinterior hboundary R hRLocation hROff hz).continuousWithinAt

/-- The completed contour integrand is continuous on the raw finite-singularity punctured
interior. -/
theorem explicitFormulaRectangleRawPuncturedInterior_continuousOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet) :
    ContinuousOn
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
      (finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaRectangleRawSingularCoordinates T)
        ε) := by
  intro z hz
  exact
    (explicitFormulaRectangleRawPuncturedInterior_continuousAt
      f F h hT hε hinterior hz).continuousWithinAt

/-- The completed contour integrand is differentiable on the raw finite-singularity
punctured interior. -/
theorem explicitFormulaRectangleRawPuncturedInterior_differentiableOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet) :
    DifferentiableOn ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
      (finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaRectangleRawSingularCoordinates T)
        ε) := by
  intro z hz
  exact
    (explicitFormulaRectangleRawPuncturedInterior_differentiableAt
      f F h hT hε hinterior hz).differentiableWithinAt

/-- The tangent-oriented boundary integral of one rectangular subdivision cell.

This is the atomic boundary expression used by the finite-hole subdivision: bottom minus
top plus `I` times right minus `I` times left, matching Mathlib's rectangle
Cauchy-Goursat convention. -/
noncomputable def finiteRectangleSubdivisionCellBoundaryIntegral
    (g : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, g (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re, g (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, g (w.re + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in z.im..w.im, g (z.re + y * Complex.I))

/-- Lower-left corner of the square of half-width `R` centered at `a`. -/
def finiteRectangleSquareLowerCorner (a : ℂ) (R : ℝ) : ℂ :=
  { re := a.re - R, im := a.im - R }

/-- Upper-right corner of the square of half-width `R` centered at `a`. -/
def finiteRectangleSquareUpperCorner (a : ℂ) (R : ℝ) : ℂ :=
  { re := a.re + R, im := a.im + R }

/-- The positive-orientation square boundary around a center, expressed as the standard
rectangular boundary of the square of half-width `R`. -/
noncomputable def finiteRectangleSquareBoundaryIntegral
    (g : ℂ → ℂ) (a : ℂ) (R : ℝ) : ℂ :=
  finiteRectangleSubdivisionCellBoundaryIntegral g
    (finiteRectangleSquareLowerCorner a R)
    (finiteRectangleSquareUpperCorner a R)

/-- Real coordinate of the lower-left square corner. -/
theorem finiteRectangleSquareLowerCorner_re (a : ℂ) (R : ℝ) :
    (finiteRectangleSquareLowerCorner a R).re = a.re - R := by
  calc
    (finiteRectangleSquareLowerCorner a R).re =
        a.re - R := by
      unfold finiteRectangleSquareLowerCorner
      rfl

/-- Imaginary coordinate of the lower-left square corner. -/
theorem finiteRectangleSquareLowerCorner_im (a : ℂ) (R : ℝ) :
    (finiteRectangleSquareLowerCorner a R).im = a.im - R := by
  calc
    (finiteRectangleSquareLowerCorner a R).im =
        a.im - R := by
      unfold finiteRectangleSquareLowerCorner
      rfl

/-- Real coordinate of the upper-right square corner. -/
theorem finiteRectangleSquareUpperCorner_re (a : ℂ) (R : ℝ) :
    (finiteRectangleSquareUpperCorner a R).re = a.re + R := by
  calc
    (finiteRectangleSquareUpperCorner a R).re =
        a.re + R := by
      unfold finiteRectangleSquareUpperCorner
      rfl

/-- Imaginary coordinate of the upper-right square corner. -/
theorem finiteRectangleSquareUpperCorner_im (a : ℂ) (R : ℝ) :
    (finiteRectangleSquareUpperCorner a R).im = a.im + R := by
  calc
    (finiteRectangleSquareUpperCorner a R).im =
        a.im + R := by
      unfold finiteRectangleSquareUpperCorner
      rfl

/-- The lower square corner lies strictly to the left of the upper square corner when
the half-width is positive. -/
theorem finiteRectangleSquareLowerCorner_re_lt_upperCorner_re
    (a : ℂ) {R : ℝ} (hR : 0 < R) :
    (finiteRectangleSquareLowerCorner a R).re <
      (finiteRectangleSquareUpperCorner a R).re := by
  calc
    (finiteRectangleSquareLowerCorner a R).re = a.re - R := by
      exact finiteRectangleSquareLowerCorner_re a R
    _ < a.re := by
      exact sub_lt_self a.re hR
    _ < a.re + R := by
      exact lt_add_of_pos_right a.re hR
    _ = (finiteRectangleSquareUpperCorner a R).re := by
      exact (finiteRectangleSquareUpperCorner_re a R).symm

/-- The lower square corner lies strictly below the upper square corner when the
half-width is positive. -/
theorem finiteRectangleSquareLowerCorner_im_lt_upperCorner_im
    (a : ℂ) {R : ℝ} (hR : 0 < R) :
    (finiteRectangleSquareLowerCorner a R).im <
      (finiteRectangleSquareUpperCorner a R).im := by
  calc
    (finiteRectangleSquareLowerCorner a R).im = a.im - R := by
      exact finiteRectangleSquareLowerCorner_im a R
    _ < a.im := by
      exact sub_lt_self a.im hR
    _ < a.im + R := by
      exact lt_add_of_pos_right a.im hR
    _ = (finiteRectangleSquareUpperCorner a R).im := by
      exact (finiteRectangleSquareUpperCorner_im a R).symm

/-- The square boundary is the subdivision-cell boundary of its lower-left and upper-right
corners. -/
theorem finiteRectangleSquareBoundaryIntegral_eq_cellBoundary
    (g : ℂ → ℂ) (a : ℂ) (R : ℝ) :
    finiteRectangleSquareBoundaryIntegral g a R =
      finiteRectangleSubdivisionCellBoundaryIntegral g
        (finiteRectangleSquareLowerCorner a R)
        (finiteRectangleSquareUpperCorner a R) := by
  rfl

/-- The square boundary unfolds to the four standard coordinate sides of the square around
the center. -/
theorem finiteRectangleSquareBoundaryIntegral_eq
    (g : ℂ → ℂ) (a : ℂ) (R : ℝ) :
    finiteRectangleSquareBoundaryIntegral g a R =
      (∫ x : ℝ in (a.re - R)..(a.re + R),
          g (x + (((a.im - R : ℝ) : ℂ) * Complex.I))) -
        (∫ x : ℝ in (a.re - R)..(a.re + R),
          g (x + (((a.im + R : ℝ) : ℂ) * Complex.I))) +
          Complex.I •
            (∫ y : ℝ in (a.im - R)..(a.im + R),
              g (((a.re + R : ℝ) : ℂ) + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in (a.im - R)..(a.im + R),
                g (((a.re - R : ℝ) : ℂ) + y * Complex.I)) := by
  unfold finiteRectangleSquareBoundaryIntegral
  unfold finiteRectangleSubdivisionCellBoundaryIntegral
  unfold finiteRectangleSquareLowerCorner
  unfold finiteRectangleSquareUpperCorner
  rfl

/-- Bottom side of the centered square boundary for the inverse kernel. -/
noncomputable def finiteRectangleSquareSubInvBottomIntegral
    (a : ℂ) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (a.re - R)..(a.re + R),
    ((x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) - a)⁻¹

/-- Top side of the centered square boundary for the inverse kernel. -/
noncomputable def finiteRectangleSquareSubInvTopIntegral
    (a : ℂ) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (a.re - R)..(a.re + R),
    ((x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) - a)⁻¹

/-- Right side of the centered square boundary for the inverse kernel, before the
standard tangent factor `I`. -/
noncomputable def finiteRectangleSquareSubInvRightIntegral
    (a : ℂ) (R : ℝ) : ℂ :=
  ∫ y : ℝ in (a.im - R)..(a.im + R),
    (((a.re + R : ℝ) : ℂ) + y * Complex.I - a)⁻¹

/-- Left side of the centered square boundary for the inverse kernel, before the
standard tangent factor `I`. -/
noncomputable def finiteRectangleSquareSubInvLeftIntegral
    (a : ℂ) (R : ℝ) : ℂ :=
  ∫ y : ℝ in (a.im - R)..(a.im + R),
    (((a.re - R : ℝ) : ℂ) + y * Complex.I - a)⁻¹

/-- Bottom-side inverse-kernel point in coordinates relative to the square center. -/
theorem finiteRectangleSquareSubInvBottom_point_sub_center
    (a : ℂ) (R x : ℝ) :
    ((x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) - a) =
      ((x - a.re : ℝ) : ℂ) + (((a.im - R) - a.im : ℝ) : ℂ) * Complex.I := by
  have hre :
      (((x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) - a).re) =
        (((x - a.re : ℝ) : ℂ) +
          (((a.im - R) - a.im : ℝ) : ℂ) * Complex.I).re := by
    calc
      (((x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) - a).re) =
          (x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ).re - a.re := by
        exact Complex.sub_re (x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) a
      _ = x - a.re := by
        exact congrArg (fun z : ℝ => z - a.re)
          (ofReal_add_mul_I_re x (a.im - R))
      _ = (((x - a.re : ℝ) : ℂ) +
          (((a.im - R) - a.im : ℝ) : ℂ) * Complex.I).re := by
        exact (ofReal_add_mul_I_re (x - a.re) ((a.im - R) - a.im)).symm
  have him :
      (((x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) - a).im) =
        (((x - a.re : ℝ) : ℂ) +
          (((a.im - R) - a.im : ℝ) : ℂ) * Complex.I).im := by
    calc
      (((x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) - a).im) =
          (x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ).im - a.im := by
        exact Complex.sub_im (x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) a
      _ = (a.im - R) - a.im := by
        exact congrArg (fun z : ℝ => z - a.im)
          (ofReal_add_mul_I_im x (a.im - R))
      _ = (((x - a.re : ℝ) : ℂ) +
          (((a.im - R) - a.im : ℝ) : ℂ) * Complex.I).im := by
        exact (ofReal_add_mul_I_im (x - a.re) ((a.im - R) - a.im)).symm
  exact Complex.ext hre him

/-- Top-side inverse-kernel point in coordinates relative to the square center. -/
theorem finiteRectangleSquareSubInvTop_point_sub_center
    (a : ℂ) (R x : ℝ) :
    ((x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) - a) =
      ((x - a.re : ℝ) : ℂ) + (((a.im + R) - a.im : ℝ) : ℂ) * Complex.I := by
  have hre :
      (((x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) - a).re) =
        (((x - a.re : ℝ) : ℂ) +
          (((a.im + R) - a.im : ℝ) : ℂ) * Complex.I).re := by
    calc
      (((x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) - a).re) =
          (x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ).re - a.re := by
        exact Complex.sub_re (x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) a
      _ = x - a.re := by
        exact congrArg (fun z : ℝ => z - a.re)
          (ofReal_add_mul_I_re x (a.im + R))
      _ = (((x - a.re : ℝ) : ℂ) +
          (((a.im + R) - a.im : ℝ) : ℂ) * Complex.I).re := by
        exact (ofReal_add_mul_I_re (x - a.re) ((a.im + R) - a.im)).symm
  have him :
      (((x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) - a).im) =
        (((x - a.re : ℝ) : ℂ) +
          (((a.im + R) - a.im : ℝ) : ℂ) * Complex.I).im := by
    calc
      (((x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) - a).im) =
          (x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ).im - a.im := by
        exact Complex.sub_im (x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) a
      _ = (a.im + R) - a.im := by
        exact congrArg (fun z : ℝ => z - a.im)
          (ofReal_add_mul_I_im x (a.im + R))
      _ = (((x - a.re : ℝ) : ℂ) +
          (((a.im + R) - a.im : ℝ) : ℂ) * Complex.I).im := by
        exact (ofReal_add_mul_I_im (x - a.re) ((a.im + R) - a.im)).symm
  exact Complex.ext hre him

/-- Right-side inverse-kernel point in coordinates relative to the square center. -/
theorem finiteRectangleSquareSubInvRight_point_sub_center
    (a : ℂ) (R y : ℝ) :
    (((a.re + R : ℝ) : ℂ) + y * Complex.I - a) =
      (((a.re + R) - a.re : ℝ) : ℂ) + ((y - a.im : ℝ) : ℂ) * Complex.I := by
  have hre :
      ((((a.re + R : ℝ) : ℂ) + y * Complex.I - a).re) =
        ((((a.re + R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).re := by
    calc
      ((((a.re + R : ℝ) : ℂ) + y * Complex.I - a).re) =
          (((a.re + R : ℝ) : ℂ) + y * Complex.I).re - a.re := by
        exact Complex.sub_re (((a.re + R : ℝ) : ℂ) + y * Complex.I) a
      _ = (a.re + R) - a.re := by
        exact congrArg (fun z : ℝ => z - a.re)
          (ofReal_add_mul_I_re (a.re + R) y)
      _ = ((((a.re + R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).re := by
        exact (ofReal_add_mul_I_re ((a.re + R) - a.re) (y - a.im)).symm
  have him :
      ((((a.re + R : ℝ) : ℂ) + y * Complex.I - a).im) =
        ((((a.re + R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).im := by
    calc
      ((((a.re + R : ℝ) : ℂ) + y * Complex.I - a).im) =
          (((a.re + R : ℝ) : ℂ) + y * Complex.I).im - a.im := by
        exact Complex.sub_im (((a.re + R : ℝ) : ℂ) + y * Complex.I) a
      _ = y - a.im := by
        exact congrArg (fun z : ℝ => z - a.im)
          (ofReal_add_mul_I_im (a.re + R) y)
      _ = ((((a.re + R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).im := by
        exact (ofReal_add_mul_I_im ((a.re + R) - a.re) (y - a.im)).symm
  exact Complex.ext hre him

/-- Left-side inverse-kernel point in coordinates relative to the square center. -/
theorem finiteRectangleSquareSubInvLeft_point_sub_center
    (a : ℂ) (R y : ℝ) :
    (((a.re - R : ℝ) : ℂ) + y * Complex.I - a) =
      (((a.re - R) - a.re : ℝ) : ℂ) + ((y - a.im : ℝ) : ℂ) * Complex.I := by
  have hre :
      ((((a.re - R : ℝ) : ℂ) + y * Complex.I - a).re) =
        ((((a.re - R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).re := by
    calc
      ((((a.re - R : ℝ) : ℂ) + y * Complex.I - a).re) =
          (((a.re - R : ℝ) : ℂ) + y * Complex.I).re - a.re := by
        exact Complex.sub_re (((a.re - R : ℝ) : ℂ) + y * Complex.I) a
      _ = (a.re - R) - a.re := by
        exact congrArg (fun z : ℝ => z - a.re)
          (ofReal_add_mul_I_re (a.re - R) y)
      _ = ((((a.re - R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).re := by
        exact (ofReal_add_mul_I_re ((a.re - R) - a.re) (y - a.im)).symm
  have him :
      ((((a.re - R : ℝ) : ℂ) + y * Complex.I - a).im) =
        ((((a.re - R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).im := by
    calc
      ((((a.re - R : ℝ) : ℂ) + y * Complex.I - a).im) =
          (((a.re - R : ℝ) : ℂ) + y * Complex.I).im - a.im := by
        exact Complex.sub_im (((a.re - R : ℝ) : ℂ) + y * Complex.I) a
      _ = y - a.im := by
        exact congrArg (fun z : ℝ => z - a.im)
          (ofReal_add_mul_I_im (a.re - R) y)
      _ = ((((a.re - R) - a.re : ℝ) : ℂ) +
          ((y - a.im : ℝ) : ℂ) * Complex.I).im := by
        exact (ofReal_add_mul_I_im ((a.re - R) - a.re) (y - a.im)).symm
  exact Complex.ext hre him

/-- The centered square boundary of the inverse kernel decomposes into the four named
real side integrals.  This is the explicit starting point for the square residue
calculation. -/
theorem finiteRectangleSquareBoundaryIntegral_sub_inv_eq_namedSides
    (a : ℂ) (R : ℝ) :
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - a)⁻¹) a R =
      finiteRectangleSquareSubInvBottomIntegral a R -
        finiteRectangleSquareSubInvTopIntegral a R +
          Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
            Complex.I • finiteRectangleSquareSubInvLeftIntegral a R := by
  exact finiteRectangleSquareBoundaryIntegral_eq (fun z : ℂ => (z - a)⁻¹) a R

/-- Fully expanded four-real-integral form of the centered square boundary for the inverse
kernel. -/
theorem finiteRectangleSquareBoundaryIntegral_sub_inv_eq_fourIntegrals
    (a : ℂ) (R : ℝ) :
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - a)⁻¹) a R =
      (∫ x : ℝ in (a.re - R)..(a.re + R),
          ((x + (((a.im - R : ℝ) : ℂ) * Complex.I) : ℂ) - a)⁻¹) -
        (∫ x : ℝ in (a.re - R)..(a.re + R),
          ((x + (((a.im + R : ℝ) : ℂ) * Complex.I) : ℂ) - a)⁻¹) +
          Complex.I •
            (∫ y : ℝ in (a.im - R)..(a.im + R),
              (((a.re + R : ℝ) : ℂ) + y * Complex.I - a)⁻¹) -
            Complex.I •
              (∫ y : ℝ in (a.im - R)..(a.im + R),
                (((a.re - R : ℝ) : ℂ) + y * Complex.I - a)⁻¹) := by
  exact finiteRectangleSquareBoundaryIntegral_eq (fun z : ℂ => (z - a)⁻¹) a R

/-- The four side evaluations imply the square inverse-kernel residue value.  The
remaining analytic work is exactly the four named side evaluations supplied here. -/
theorem finiteRectangleSquareBoundaryIntegral_sub_inv_eq_twoPiI_of_sideValues
    (a : ℂ) (R : ℝ)
    (hbottom :
      finiteRectangleSquareSubInvBottomIntegral a R =
        (Real.pi / 2 : ℂ) * Complex.I)
    (htop :
      finiteRectangleSquareSubInvTopIntegral a R =
        -(Real.pi / 2 : ℂ) * Complex.I)
    (hright :
      Complex.I • finiteRectangleSquareSubInvRightIntegral a R =
        (Real.pi / 2 : ℂ) * Complex.I)
    (hleft :
      Complex.I • finiteRectangleSquareSubInvLeftIntegral a R =
        -(Real.pi / 2 : ℂ) * Complex.I) :
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - a)⁻¹) a R =
      (2 * Real.pi * Complex.I : ℂ) := by
  let q : ℂ := (Real.pi / 2 : ℂ) * Complex.I
  have hboundary :
      finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - a)⁻¹) a R =
        finiteRectangleSquareSubInvBottomIntegral a R -
          finiteRectangleSquareSubInvTopIntegral a R +
            Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R :=
    finiteRectangleSquareBoundaryIntegral_sub_inv_eq_namedSides a R
  have htopQ :
      finiteRectangleSquareSubInvTopIntegral a R = -q := by
    calc
      finiteRectangleSquareSubInvTopIntegral a R =
          -(Real.pi / 2 : ℂ) * Complex.I := by
        exact htop
      _ = -q := by
        exact neg_mul (Real.pi / 2 : ℂ) Complex.I
  have hleftQ :
      Complex.I • finiteRectangleSquareSubInvLeftIntegral a R = -q := by
    calc
      Complex.I • finiteRectangleSquareSubInvLeftIntegral a R =
          -(Real.pi / 2 : ℂ) * Complex.I := by
        exact hleft
      _ = -q := by
        exact neg_mul (Real.pi / 2 : ℂ) Complex.I
  have hfour :
      finiteRectangleSquareSubInvBottomIntegral a R -
        finiteRectangleSquareSubInvTopIntegral a R +
          Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
            Complex.I • finiteRectangleSquareSubInvLeftIntegral a R =
        q + q + q + q := by
    calc
      finiteRectangleSquareSubInvBottomIntegral a R -
          finiteRectangleSquareSubInvTopIntegral a R +
            Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R =
          q - finiteRectangleSquareSubInvTopIntegral a R +
            Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R := by
        exact congrArg
          (fun z : ℂ =>
            z - finiteRectangleSquareSubInvTopIntegral a R +
              Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
                Complex.I • finiteRectangleSquareSubInvLeftIntegral a R)
          hbottom
      _ = q - (-q) + Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R := by
        exact congrArg
          (fun z : ℂ =>
            q - z + Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R)
          htopQ
      _ = q + q + Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R := by
        exact congrArg
          (fun z : ℂ =>
            z + Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R)
          (sub_neg_eq_add q q)
      _ = q + q + q - Complex.I • finiteRectangleSquareSubInvLeftIntegral a R := by
        exact congrArg
          (fun z : ℂ => q + q + z - Complex.I • finiteRectangleSquareSubInvLeftIntegral a R)
          hright
      _ = q + q + q - (-q) := by
        exact congrArg (fun z : ℂ => q + q + q - z) hleftQ
      _ = q + q + q + q := by
        exact sub_neg_eq_add (q + q + q) q
  have htwice : q + q = (Real.pi : ℂ) * Complex.I := by
    calc
      q + q = (Real.pi / 2 : ℂ) * Complex.I +
          (Real.pi / 2 : ℂ) * Complex.I := by
        rfl
      _ = ((Real.pi / 2 : ℂ) + (Real.pi / 2 : ℂ)) * Complex.I := by
        exact (add_mul (Real.pi / 2 : ℂ) (Real.pi / 2 : ℂ) Complex.I).symm
      _ = (Real.pi : ℂ) * Complex.I := by
        exact congrArg (fun z : ℂ => z * Complex.I) (add_halves (Real.pi : ℂ))
  have hfour_eval : q + q + q + q = (2 * Real.pi * Complex.I : ℂ) := by
    calc
      q + q + q + q = (q + q) + (q + q) := by
        exact add_assoc (q + q) q q
      _ = (Real.pi : ℂ) * Complex.I + (q + q) := by
        exact congrArg (fun z : ℂ => z + (q + q)) htwice
      _ = (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
        exact congrArg (fun z : ℂ => (Real.pi : ℂ) * Complex.I + z) htwice
      _ = ((Real.pi : ℂ) + (Real.pi : ℂ)) * Complex.I := by
        exact (add_mul (Real.pi : ℂ) (Real.pi : ℂ) Complex.I).symm
      _ = (2 * Real.pi : ℂ) * Complex.I := by
        exact congrArg (fun z : ℂ => z * Complex.I) (two_mul (Real.pi : ℂ)).symm
      _ = (2 * Real.pi * Complex.I : ℂ) := by
        rfl
  calc
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - a)⁻¹) a R =
        finiteRectangleSquareSubInvBottomIntegral a R -
          finiteRectangleSquareSubInvTopIntegral a R +
            Complex.I • finiteRectangleSquareSubInvRightIntegral a R -
              Complex.I • finiteRectangleSquareSubInvLeftIntegral a R := by
      exact hboundary
    _ = q + q + q + q := by
      exact hfour
    _ = (2 * Real.pi * Complex.I : ℂ) := by
      exact hfour_eval

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
