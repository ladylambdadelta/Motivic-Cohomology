import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Single-pole contour owner API

This file owns the isolated one-pole contour objects used by the vertical
channel and finite-rectangle residue layers.  It sits below both consumers so
the finite single-pole Cauchy theorem can be added here without creating the
`VerticalChannels` / `FiniteRectangleResidues` cycle.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- The isolated `s = 1` correction kernel as a function of the contour variable.

This is the object to which finite Cauchy/residue calculus applies.  The real
side integrals below integrate this kernel after parametrization; the genuine
complex contour integral must also include the tangent of each parametrized side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  (-1 / (z - 1)) * zetaCompletedExplicitFormulaPhi f (z - 1 / 2)

/-- The tangent-weighted right side of the isolated `s = 1` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) * Complex.I

/-- The tangent-weighted left side of the isolated `s = 1` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) * Complex.I

/-- The tangent-weighted top side of the isolated `s = 1` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)

/-- The tangent-weighted bottom side of the isolated `s = 1` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)

/-- The genuine tangent-weighted rectangle contour integral for the isolated
`s = 1` correction kernel.  This is the owner-level boundary object for the
finite isolated-pole Cauchy/residue theorem. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T +
      zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T

/-- The tangent-weighted isolated `s = 1` rectangle boundary integral unfolds to
its four oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T :=
  rfl

/-- The standard positively oriented rectangle boundary expression for the
isolated `s = 1` kernel, in Mathlib's rectangle-Cauchy convention. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ x in Set.Icc (1 - F.c) F.c,
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) -
    (∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) +
      zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T

/-- The standard `s = 1` rectangle boundary expression unfolds to Mathlib's
bottom-minus-top plus right-minus-left tangent convention. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral f F T =
      (∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) -
        (∫ x in Set.Icc (1 - F.c) F.c,
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) +
          zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T :=
  rfl

/-- The project-normalized standard rectangle boundary for the isolated
`s = 1` kernel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral f F T

/-- The normalized `s = 1` standard rectangle boundary unfolds to `(2πi)⁻¹`
times the raw standard contour boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F T :=
  rfl

/-- Transport from the raw standard finite Cauchy theorem for the isolated
`s = 1` kernel, with its `2πi` factor, to the project-normalized residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral_eq_residue_of_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hraw :
      zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F T =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
      -zetaCompletedExplicitFormulaPhi f (1 / 2) := by
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let R : ℂ := -zetaCompletedExplicitFormulaPhi f (1 / 2)
  have hnorm :
      zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral
          f F T =
        C⁻¹ *
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T := by
    rfl
  have hraw' :
      zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F T = C * R :=
    hraw
  have hC_ne : C ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (show (2 : ℝ) ≠ 0 from two_ne_zero))
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
        C⁻¹ *
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T := hnorm
    _ = C⁻¹ * (C * R) := by
      exact congrArg (fun z : ℂ => C⁻¹ * z) hraw'
    _ = (C⁻¹ * C) * R := by
      exact (mul_assoc C⁻¹ C R).symm
    _ = 1 * R := by
      exact congrArg (fun z : ℂ => z * R) (inv_mul_cancel₀ hC_ne)
    _ = R := by
      exact one_mul R

/-- In the pole-enclosing geometry, the unordered horizontal span is the
left-to-right closed interval used by a standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaSinglePoleHorizontal_uIcc_eq_Icc
    (F : ExplicitFormulaContourFamily) :
    Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c := by
  have hleft_lt_right : 1 - F.c < F.c :=
    lt_trans F.one_sub_c_neg F.c_pos
  exact Set.uIcc_of_ge (le_of_lt hleft_lt_right)

/-- The top tangent edge of the isolated `s = 1` correction contour can be read
over the left-to-right horizontal interval. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T =
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) := by
  exact congrArg
    (fun s : Set ℝ =>
      ∫ x in s,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x))
    (zetaCompletedExplicitFormulaSinglePoleHorizontal_uIcc_eq_Icc F)

/-- The bottom tangent edge of the isolated `s = 1` correction contour can be
read over the left-to-right horizontal interval. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T =
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) := by
  exact congrArg
    (fun s : Set ℝ =>
      ∫ x in s,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x))
    (zetaCompletedExplicitFormulaSinglePoleHorizontal_uIcc_eq_Icc F)

/-- The isolated `s = 1` tangent rectangle boundary with the horizontal sides
written in left-to-right rectangle coordinates. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eq_IccHorizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T +
          (∫ x in Set.Icc (1 - F.c) F.c,
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) -
            (∫ x in Set.Icc (1 - F.c) F.c,
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
                (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) := by
  let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T
  let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T
  let U : ℂ := zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T
  let B : ℂ := zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T
  let U' : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)
  let B' : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)
  have hU : U = U' :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_Icc
      f F T
  have hB : B = B' :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_Icc
      f F T
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        R - L + U - B := by
      rfl
    _ = R - L + U' - B := by
      exact congrArg (fun x : ℂ => R - L + x - B) hU
    _ = R - L + U' - B' := by
      exact congrArg (fun x : ℂ => R - L + U' - x) hB

/-- One-coordinate deleted-circle residue theorem in Mathlib's circle normalization.

This is the non-cyclic simple-pole analytic primitive used by finite rectangle
residue constructions: a punctured local coefficient limit gives the raw
deleted-circle boundary value with the unavoidable `2πi` factor. -/
theorem zetaExplicitFormulaSinglePole_deletedCircleCoefficientIntegral_eq_twoPiI_smul_residue
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

/-- One-coordinate deleted-circle residue theorem for an actual meromorphic
integrand, stated through its local coefficient `(z - c) * g z`. -/
theorem zetaExplicitFormulaSinglePole_deletedCircleIntegral_eq_twoPiI_smul_residue
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
        zetaExplicitFormulaSinglePole_deletedCircleCoefficientIntegral_eq_twoPiI_smul_residue
          hR
          (fun z : ℂ => (z - c) * g z)
          residue
          s
          hs
          hcontinuous
          hdifferentiable
          hlocal

/-- The tangent-oriented boundary integral of one rectangular subdivision cell,
using Mathlib's rectangle Cauchy-Goursat convention. -/
noncomputable def zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    (g : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, g (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re, g (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, g (w.re + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in z.im..w.im, g (z.re + y * Complex.I))

/-- Cauchy-Goursat for one regular subdivision cell. -/
theorem zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
    (g : ℂ → ℂ) (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im) \ s →
          DifferentiableAt ℂ g x) :
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral g z w = 0 := by
  exact
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      g z w s hs Hc Hd

/-- Cauchy-Goursat for one regular subdivision cell with no exceptional set. -/
theorem zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiableOn
    (g : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd :
      DifferentiableOn ℂ g
        (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
          Set.Ioo (min z.im w.im) (max z.im w.im))) :
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral g z w = 0 := by
  exact
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      g z w Hc Hd

/-- A finite subdivision boundary sum vanishes when each cell boundary vanishes. -/
theorem zetaExplicitFormulaSinglePoleSubdivisionBoundarySum_eq_zero_of_cellBoundaries
    {ι : Type*} [DecidableEq ι] (cells : Finset ι) (cellBoundary : ι → ℂ)
    (hcell : ∀ c : ι, c ∈ cells → cellBoundary c = 0) :
    (∑ c in cells, cellBoundary c) = 0 := by
  exact Finset.sum_eq_zero hcell

/-- A finite rectangular subdivision has zero total boundary when each cell
satisfies the rectangular Cauchy-Goursat hypotheses. -/
theorem zetaExplicitFormulaSinglePoleSubdivisionBoundarySum_eq_zero_of_cellCauchy
    {ι : Type*} [DecidableEq ι] (cells : Finset ι) (g : ℂ → ℂ)
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
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g (lower c) (upper c)) = 0 := by
  exact
    zetaExplicitFormulaSinglePoleSubdivisionBoundarySum_eq_zero_of_cellBoundaries
      cells
      (fun c : ι =>
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g (lower c) (upper c))
      (fun c hc =>
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
          g (lower c) (upper c) (s c) (hs c hc) (Hc c hc) (Hd c hc))

/-- Transport zero from a concrete subdivision boundary sum to the named
outer-minus-inner punctured-rectangle boundary expression.  The equality input
is the geometric edge-cancellation theorem for the chosen finite subdivision. -/
theorem zetaExplicitFormulaSinglePolePuncturedRectangleBoundary_eq_zero_of_subdivisionBoundary
    {ι : Type*} [DecidableEq ι] (cells : Finset ι) (cellBoundary : ι → ℂ)
    (puncturedBoundary : ℂ)
    (hsubdivision : puncturedBoundary = ∑ c in cells, cellBoundary c)
    (hcellZero : ∀ c : ι, c ∈ cells → cellBoundary c = 0) :
    puncturedBoundary = 0 := by
  have hsum :
      (∑ c in cells, cellBoundary c) = 0 :=
    zetaExplicitFormulaSinglePoleSubdivisionBoundarySum_eq_zero_of_cellBoundaries
      cells cellBoundary hcellZero
  calc
    puncturedBoundary = ∑ c in cells, cellBoundary c := hsubdivision
    _ = 0 := hsum

/-- Standard rectangle boundary integral in coordinate form, using Mathlib's
bottom-minus-top plus right-minus-left convention. -/
noncomputable def zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
    (g : ℂ → ℂ) (left right bottom top : ℝ) : ℂ :=
  (∫ x : ℝ in left..right, g (x + bottom * Complex.I)) -
    (∫ x : ℝ in left..right, g (x + top * Complex.I)) +
      Complex.I • (∫ y : ℝ in bottom..top, g (right + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in bottom..top, g (left + y * Complex.I))

/-- Standard boundary integral of the square puncture centered at `1` with
half-width `R`.  This is the inner rectangular boundary produced by finite
rectangular cell cancellation. -/
noncomputable def zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
    g (1 - R) (1 + R) (-R) R

/-- The outer rectangle boundary for a contour family, expressed in the same
coordinate convention as Mathlib's rectangle Cauchy theorem. -/
noncomputable def zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
    g (1 - F.c) F.c (-T) T

/-- The bottom cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `1`. -/
noncomputable def zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g ((1 - F.c) + (-T) * Complex.I) (F.c + (-R) * Complex.I)

/-- The top cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `1`. -/
noncomputable def zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g ((1 - F.c) + R * Complex.I) (F.c + T * Complex.I)

/-- The left cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `1`. -/
noncomputable def zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g ((1 - F.c) + (-R) * Complex.I) ((1 - R) + R * Complex.I)

/-- The right cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `1`. -/
noncomputable def zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g ((1 + R) + (-R) * Complex.I) (F.c + R * Complex.I)

/-- The finite four-cell boundary sum for the rectangle with the one-pole inner
square removed. -/
noncomputable def zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R +
    zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R +
      zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R +
        zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R

/-- The finite square-punctured rectangle boundary: outer standard boundary
minus the inner square boundary.  The next geometric cancellation theorem
identifies this with the four-cell boundary sum. -/
noncomputable def zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T -
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R

/-- The named outer boundary coordinate integral unfolds to the standard
rectangle convention. -/
theorem zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T =
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
        g (1 - F.c) F.c (-T) T :=
  rfl

/-- The named inner square boundary unfolds to the standard rectangle
convention around the pole `1`. -/
theorem zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral_eq
    (g : ℂ → ℂ) (R : ℝ) :
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R =
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
        g (1 - R) (1 + R) (-R) R :=
  rfl

/-- The named finite square-punctured rectangle boundary unfolds to
outer-minus-inner. -/
theorem zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T -
        zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R :=
  rfl

/-- The bottom cell boundary unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R =
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I)) := by
  rfl

/-- The top cell boundary unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R =
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I)) := by
  rfl

/-- The left cell boundary unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R =
      (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I)) := by
  rfl

/-- The right cell boundary unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R =
      (∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) -
        (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I)) := by
  rfl

/-- The four-cell one-pole punctured rectangle boundary is the ordered sum of
the bottom, top, left, and right cell boundaries. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_cells
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
      zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R +
        zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R +
          zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R +
            zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R := by
  rfl

/-- The four-cell boundary sum unfolds to the sum of the four explicit
coordinate cell boundaries. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_expandedCells
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) +
            ((∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) -
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I))) := by
  let B : ℂ := zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R
  let U : ℂ := zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R
  let L : ℂ := zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R
  let Q : ℂ := zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R
  have hB : B =
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I)) :=
    zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral_eq g F T R
  have hU : U =
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I)) :=
    zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral_eq g F T R
  have hL : L =
      (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I)) :=
    zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral_eq g F T R
  have hQ : Q =
      (∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) -
        (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I)) :=
    zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral_eq g F T R
  calc
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
        B + U + L + Q := by
      rfl
    _ =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) + U + L + Q := by
      exact congrArg (fun z : ℂ => z + U + L + Q) hB
    _ =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) + L + Q := by
      exact congrArg
        (fun z : ℂ =>
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
            z + L + Q)
        hU
    _ =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) + Q := by
      exact congrArg
        (fun z : ℂ =>
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
            ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) +
              z + Q)
        hL
    _ =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) +
            ((∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) -
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I)) ) := by
      exact congrArg
        (fun z : ℂ =>
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
            ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) +
              ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
                (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
                  Complex.I •
                    (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
                    Complex.I •
                      (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) +
                z)
        hQ

/-- The right side path is the raw coordinate line `F.c + t I`. -/
theorem zetaExplicitFormulaOnePole_rightPath_eq_coordinate
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t =
      F.c + t * Complex.I := by
  rfl

/-- The left side path is the raw coordinate line `(1 - F.c) + t I`. -/
theorem zetaExplicitFormulaOnePole_leftPath_eq_coordinate
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t =
      (1 - F.c) + t * Complex.I := by
  rfl

/-- The top side path is the raw coordinate line `x + T I`. -/
theorem zetaExplicitFormulaOnePole_topPath_eq_coordinate
    (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    zetaCompletedExplicitFormulaTopPath (F.rectangle T) x =
      x + T * Complex.I := by
  rfl

/-- The bottom side path is the raw coordinate line `x + (-T) I`. -/
theorem zetaExplicitFormulaOnePole_bottomPath_eq_coordinate
    (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x =
      x + (-T) * Complex.I := by
  calc
    zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x =
        x - T * Complex.I := by
      rfl
    _ = x + -(T * Complex.I) := by
      exact sub_eq_add_neg x (T * Complex.I)
    _ = x + (-T) * Complex.I := by
      exact congrArg (fun z : ℂ => x + z) (neg_mul T Complex.I).symm

/-- The one-pole kernel along the right path is the corresponding raw
coordinate integrand. -/
theorem zetaExplicitFormulaOnePole_rightPath_integrand_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (F.c + t * Complex.I) := by
  exact congrArg
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    (zetaExplicitFormulaOnePole_rightPath_eq_coordinate F T t)

/-- The one-pole kernel along the left path is the corresponding raw coordinate
integrand. -/
theorem zetaExplicitFormulaOnePole_leftPath_integrand_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        ((1 - F.c) + t * Complex.I) := by
  exact congrArg
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    (zetaExplicitFormulaOnePole_leftPath_eq_coordinate F T t)

/-- The one-pole kernel along the top path is the corresponding raw coordinate
integrand. -/
theorem zetaExplicitFormulaOnePole_topPath_integrand_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (x + T * Complex.I) := by
  exact congrArg
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    (zetaExplicitFormulaOnePole_topPath_eq_coordinate F T x)

/-- The one-pole kernel along the bottom path is the corresponding raw
coordinate integrand. -/
theorem zetaExplicitFormulaOnePole_bottomPath_integrand_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (x + (-T) * Complex.I) := by
  exact congrArg
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    (zetaExplicitFormulaOnePole_bottomPath_eq_coordinate F T x)

/-- On a left-to-right real interval, the set integral over `Icc` is the
corresponding interval integral. -/
theorem zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
    (φ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Icc a b, φ x) = ∫ x : ℝ in a..b, φ x := by
  have hinterval :
      (∫ x : ℝ in a..b, φ x) = ∫ x in Set.Ioc a b, φ x :=
    intervalIntegral.integral_of_le hab
  have hset :
      (∫ x in Set.Icc a b, φ x) = ∫ x in Set.Ioc a b, φ x :=
    MeasureTheory.integral_Icc_eq_integral_Ioc
  exact Eq.trans hset hinterval.symm

/-- Multiplication by the tangent `I` can be pulled out of a one-dimensional
interval integral in the right-multiplication convention. -/
theorem zetaExplicitFormulaSinglePole_intervalIntegral_mul_I
    (φ : ℝ → ℂ) (a b : ℝ) :
    (∫ x : ℝ in a..b, φ x * Complex.I) =
      (∫ x : ℝ in a..b, φ x) * Complex.I := by
  exact intervalIntegral.integral_mul_const Complex.I φ

/-- Right multiplication by `I` is the same tangent factor as scalar
multiplication by `I` on complex-valued interval integrals. -/
theorem zetaExplicitFormulaSinglePole_intervalIntegral_mul_I_eq_smul
    (φ : ℝ → ℂ) (a b : ℝ) :
    (∫ x : ℝ in a..b, φ x) * Complex.I =
      Complex.I • (∫ x : ℝ in a..b, φ x) := by
  let J : ℂ := ∫ x : ℝ in a..b, φ x
  calc
    (∫ x : ℝ in a..b, φ x) * Complex.I = J * Complex.I := by
      rfl
    _ = Complex.I * J := by
      exact mul_comm J Complex.I
    _ = Complex.I • J := by
      exact (smul_eq_mul Complex.I J).symm

/-- The right one-pole tangent side is the coordinate vertical edge integral in
Mathlib's rectangle convention. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T =
      Complex.I •
        (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (F.c + y * Complex.I)) := by
  let φ : ℝ → ℂ :=
    fun y : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (F.c + y * Complex.I)
  let ψ : ℝ → ℂ :=
    fun y : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) y)
  have hpoint :
      (fun y : ℝ => ψ y * Complex.I) =
        (fun y : ℝ => φ y * Complex.I) := by
    funext y
    exact congrArg
      (fun z : ℂ => z * Complex.I)
      (zetaExplicitFormulaOnePole_rightPath_integrand_eq_coordinate f F T y)
  have hset :
      (∫ y in Set.Icc (-T) T, ψ y * Complex.I) =
        ∫ y in Set.Icc (-T) T, φ y * Complex.I :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun y _hy => congrFun hpoint y)
  have hinterval :
      (∫ y in Set.Icc (-T) T, φ y * Complex.I) =
        ∫ y : ℝ in -T..T, φ y * Complex.I :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      (fun y : ℝ => φ y * Complex.I)
      (neg_nonpos.mpr hT)
  calc
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T =
        ∫ y in Set.Icc (-T) T, ψ y * Complex.I := by
      rfl
    _ = ∫ y in Set.Icc (-T) T, φ y * Complex.I := hset
    _ = ∫ y : ℝ in -T..T, φ y * Complex.I := hinterval
    _ = (∫ y : ℝ in -T..T, φ y) * Complex.I := by
      exact zetaExplicitFormulaSinglePole_intervalIntegral_mul_I φ (-T) T
    _ = Complex.I • (∫ y : ℝ in -T..T, φ y) := by
      exact zetaExplicitFormulaSinglePole_intervalIntegral_mul_I_eq_smul φ (-T) T

/-- The left one-pole tangent side is the coordinate vertical edge integral in
Mathlib's rectangle convention. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) :
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T =
      Complex.I •
        (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            ((1 - F.c) + y * Complex.I)) := by
  let φ : ℝ → ℂ :=
    fun y : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        ((1 - F.c) + y * Complex.I)
  let ψ : ℝ → ℂ :=
    fun y : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) y)
  have hpoint :
      (fun y : ℝ => ψ y * Complex.I) =
        (fun y : ℝ => φ y * Complex.I) := by
    funext y
    exact congrArg
      (fun z : ℂ => z * Complex.I)
      (zetaExplicitFormulaOnePole_leftPath_integrand_eq_coordinate f F T y)
  have hset :
      (∫ y in Set.Icc (-T) T, ψ y * Complex.I) =
        ∫ y in Set.Icc (-T) T, φ y * Complex.I :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun y _hy => congrFun hpoint y)
  have hinterval :
      (∫ y in Set.Icc (-T) T, φ y * Complex.I) =
        ∫ y : ℝ in -T..T, φ y * Complex.I :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      (fun y : ℝ => φ y * Complex.I)
      (neg_nonpos.mpr hT)
  calc
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T =
        ∫ y in Set.Icc (-T) T, ψ y * Complex.I := by
      rfl
    _ = ∫ y in Set.Icc (-T) T, φ y * Complex.I := hset
    _ = ∫ y : ℝ in -T..T, φ y * Complex.I := hinterval
    _ = (∫ y : ℝ in -T..T, φ y) * Complex.I := by
      exact zetaExplicitFormulaSinglePole_intervalIntegral_mul_I φ (-T) T
    _ = Complex.I • (∫ y : ℝ in -T..T, φ y) := by
      exact zetaExplicitFormulaSinglePole_intervalIntegral_mul_I_eq_smul φ (-T) T

/-- The named one-pole standard rectangle boundary is the coordinate outer
standard rectangle boundary at nonnegative height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_coordinateOuter
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral f F T =
      zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T := by
  let g : ℂ → ℂ :=
    fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z
  let Bset : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)
  let Tset : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)
  let Bcoord : ℂ :=
    ∫ x : ℝ in (1 - F.c)..F.c,
      g (x + (-T) * Complex.I)
  let Tcoord : ℂ :=
    ∫ x : ℝ in (1 - F.c)..F.c,
      g (x + T * Complex.I)
  let Rcoord : ℂ :=
    Complex.I •
      (∫ y : ℝ in -T..T,
        g (F.c + y * Complex.I))
  let Lcoord : ℂ :=
    Complex.I •
      (∫ y : ℝ in -T..T,
        g ((1 - F.c) + y * Complex.I))
  have hleft_right : 1 - F.c ≤ F.c :=
    le_of_lt (lt_trans F.one_sub_c_neg F.c_pos)
  have hbottom_point :
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) =
        (fun x : ℝ => g (x + (-T) * Complex.I)) := by
    funext x
    exact zetaExplicitFormulaOnePole_bottomPath_integrand_eq_coordinate f F T x
  have htop_point :
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) =
        (fun x : ℝ => g (x + T * Complex.I)) := by
    funext x
    exact zetaExplicitFormulaOnePole_topPath_integrand_eq_coordinate f F T x
  have hbottom_set :
      Bset = Bcoord := by
    have hcongr :
        Bset =
          ∫ x in Set.Icc (1 - F.c) F.c, g (x + (-T) * Complex.I) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun x _hx => congrFun hbottom_point x)
    have hinterval :
        (∫ x in Set.Icc (1 - F.c) F.c, g (x + (-T) * Complex.I)) =
          ∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I) :=
      zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
        (fun x : ℝ => g (x + (-T) * Complex.I))
        hleft_right
    exact Eq.trans hcongr hinterval
  have htop_set :
      Tset = Tcoord := by
    have hcongr :
        Tset =
          ∫ x in Set.Icc (1 - F.c) F.c, g (x + T * Complex.I) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun x _hx => congrFun htop_point x)
    have hinterval :
        (∫ x in Set.Icc (1 - F.c) F.c, g (x + T * Complex.I)) =
          ∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I) :=
      zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
        (fun x : ℝ => g (x + T * Complex.I))
        hleft_right
    exact Eq.trans hcongr hinterval
  have hright :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T =
        Rcoord :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_coordinate
      f F hT
  have hleft :
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T =
        Lcoord :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_coordinate
      f F hT
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral f F T =
        Bset - Tset +
          zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
      rfl
    _ = Bcoord - Tset +
          zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
      exact congrArg
        (fun z : ℂ =>
          z - Tset +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T)
        hbottom_set
    _ = Bcoord - Tcoord +
          zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
      exact congrArg
        (fun z : ℂ =>
          Bcoord - z +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T)
        htop_set
    _ = Bcoord - Tcoord + Rcoord -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
      exact congrArg
        (fun z : ℂ =>
          Bcoord - Tcoord + z -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T)
        hright
    _ = Bcoord - Tcoord + Rcoord - Lcoord := by
      exact congrArg
        (fun z : ℂ => Bcoord - Tcoord + Rcoord - z)
        hleft
    _ =
      zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T := by
      rfl

/-- Two adjacent interval integrals combine into the integral over their union,
in the orientation convention used by rectangle edges. -/
theorem zetaExplicitFormulaSinglePole_intervalIntegral_split_two
    (φ : ℝ → ℂ) (a b c : ℝ)
    (hab : IntervalIntegrable φ volume a b)
    (hbc : IntervalIntegrable φ volume b c) :
    (∫ x : ℝ in a..b, φ x) + (∫ x : ℝ in b..c, φ x) =
      ∫ x : ℝ in a..c, φ x := by
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- Three adjacent interval integrals combine into the integral over their
outer endpoints. -/
theorem zetaExplicitFormulaSinglePole_intervalIntegral_split_three
    (φ : ℝ → ℂ) (a b c d : ℝ)
    (hab : IntervalIntegrable φ volume a b)
    (hbc : IntervalIntegrable φ volume b c)
    (hcd : IntervalIntegrable φ volume c d) :
    ((∫ x : ℝ in a..b, φ x) + (∫ x : ℝ in b..c, φ x)) +
        (∫ x : ℝ in c..d, φ x) =
      ∫ x : ℝ in a..d, φ x := by
  have habc :
      (∫ x : ℝ in a..b, φ x) + (∫ x : ℝ in b..c, φ x) =
        ∫ x : ℝ in a..c, φ x :=
    zetaExplicitFormulaSinglePole_intervalIntegral_split_two
      φ a b c hab hbc
  have hac : IntervalIntegrable φ volume a c :=
    hab.trans hbc
  have hacd :
      (∫ x : ℝ in a..c, φ x) + (∫ x : ℝ in c..d, φ x) =
        ∫ x : ℝ in a..d, φ x :=
    zetaExplicitFormulaSinglePole_intervalIntegral_split_two
      φ a c d hac hcd
  calc
    ((∫ x : ℝ in a..b, φ x) + (∫ x : ℝ in b..c, φ x)) +
        (∫ x : ℝ in c..d, φ x) =
        (∫ x : ℝ in a..c, φ x) + (∫ x : ℝ in c..d, φ x) := by
      exact congrArg
        (fun z : ℂ => z + (∫ x : ℝ in c..d, φ x))
        habc
    _ = ∫ x : ℝ in a..d, φ x := hacd

/-- Two adjacent vertical rectangle-edge integrals combine after applying the
standard tangent factor `I`. -/
theorem zetaExplicitFormulaSinglePole_verticalIntegral_split_two
    (φ : ℝ → ℂ) (a b c : ℝ)
    (hab : IntervalIntegrable φ volume a b)
    (hbc : IntervalIntegrable φ volume b c) :
    Complex.I • ((∫ y : ℝ in a..b, φ y) + (∫ y : ℝ in b..c, φ y)) =
      Complex.I • (∫ y : ℝ in a..c, φ y) := by
  exact congrArg
    (fun z : ℂ => Complex.I • z)
    (zetaExplicitFormulaSinglePole_intervalIntegral_split_two
      φ a b c hab hbc)

/-- Three adjacent vertical rectangle-edge integrals combine after applying the
standard tangent factor `I`. -/
theorem zetaExplicitFormulaSinglePole_verticalIntegral_split_three
    (φ : ℝ → ℂ) (a b c d : ℝ)
    (hab : IntervalIntegrable φ volume a b)
    (hbc : IntervalIntegrable φ volume b c)
    (hcd : IntervalIntegrable φ volume c d) :
    Complex.I •
        (((∫ y : ℝ in a..b, φ y) + (∫ y : ℝ in b..c, φ y)) +
          (∫ y : ℝ in c..d, φ y)) =
      Complex.I • (∫ y : ℝ in a..d, φ y) := by
  exact congrArg
    (fun z : ℂ => Complex.I • z)
    (zetaExplicitFormulaSinglePole_intervalIntegral_split_three
      φ a b c d hab hbc hcd)

/-- The right outer vertical side is the sum of the three right vertical
segments in the four-cell one-pole decomposition. -/
theorem zetaExplicitFormulaOnePole_rightOuterVertical_eq_threeSegments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I)) volume (-T) (-R))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I)) volume (-R) R)
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I)) volume R T) :
    (Complex.I •
        (((∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) +
          (∫ y : ℝ in -R..R, g (F.c + y * Complex.I))) +
            (∫ y : ℝ in R..T, g (F.c + y * Complex.I)))) =
      Complex.I •
        (∫ y : ℝ in -T..T, g (F.c + y * Complex.I)) := by
  exact
    zetaExplicitFormulaSinglePole_verticalIntegral_split_three
      (fun y : ℝ => g (F.c + y * Complex.I))
      (-T) (-R) R T
      hbottom hmiddle htop

/-- The left outer vertical side is the sum of the three left vertical
segments in the four-cell one-pole decomposition. -/
theorem zetaExplicitFormulaOnePole_leftOuterVertical_eq_threeSegments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I)) volume (-T) (-R))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I)) volume (-R) R)
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I)) volume R T) :
    (Complex.I •
        (((∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I)) +
          (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) +
            (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I)))) =
      Complex.I •
        (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I)) := by
  exact
    zetaExplicitFormulaSinglePole_verticalIntegral_split_three
      (fun y : ℝ => g ((1 - F.c) + y * Complex.I))
      (-T) (-R) R T
      hbottom hmiddle htop

/-- The bottom horizontal line at the puncture height splits into left,
inner-square, and right pieces. -/
theorem zetaExplicitFormulaOnePole_bottomPunctureHorizontal_threeSegments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I)) volume (1 - F.c) (1 - R))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I)) volume (1 - R) (1 + R))
    (hright :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I)) volume (1 + R) F.c) :
    ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) +
        (∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I))) +
          (∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) =
      ∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I) := by
  exact
    zetaExplicitFormulaSinglePole_intervalIntegral_split_three
      (fun x : ℝ => g (x + (-R) * Complex.I))
      (1 - F.c) (1 - R) (1 + R) F.c
      hleft hinner hright

/-- The top horizontal line at the puncture height splits into left,
inner-square, and right pieces. -/
theorem zetaExplicitFormulaOnePole_topPunctureHorizontal_threeSegments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (1 - F.c) (1 - R))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (1 - R) (1 + R))
    (hright :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (1 + R) F.c) :
    ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
        (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
          (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) =
      ∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I) := by
  exact
    zetaExplicitFormulaSinglePole_intervalIntegral_split_three
      (fun x : ℝ => g (x + R * Complex.I))
      (1 - F.c) (1 - R) (1 + R) F.c
      hleft hinner hright

/-- Square-punctured boundary accounting: if the punctured boundary is zero
and the inner square boundary has value `A`, then the outer standard boundary
has value `A`. -/
theorem zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral_eq_of_squarePuncturedBoundary_zero
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) (A : ℂ)
    (hcauchy :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        g F T R = 0)
    (hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R = A) :
    zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T = A := by
  let O : ℂ := zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T
  let I : ℂ := zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R
  have hpunctured : O - I = 0 := by
    calc
      O - I =
          zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
            g F T R := by
        exact
          (zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral_eq
            g F T R).symm
      _ = 0 := hcauchy
  have houter_eq_inner : O = I := by
    calc
      O = (O - I) + I := by
        exact (sub_add_cancel O I).symm
      _ = 0 + I := by
        exact congrArg (fun z : ℂ => z + I) hpunctured
      _ = I := by
        exact zero_add I
  calc
    zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T =
        O := by
      rfl
    _ = I := houter_eq_inner
    _ = A := hinner

/-- For the isolated `s = 1` kernel, the named standard rectangle boundary
minus the inner square boundary is exactly the square-punctured rectangle
boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardBoundary_sub_innerSquare_eq_squarePunctured
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) (R : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F T -
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        R =
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R := by
  let g : ℂ → ℂ :=
    fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z
  let S : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T
  let O : ℂ := zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T
  let I : ℂ := zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R
  have hstandard : S = O :=
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_coordinateOuter
      f F hT
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F T -
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        R =
        S - I := by
      rfl
    _ = O - I := by
      exact congrArg (fun z : ℂ => z - I) hstandard
    _ =
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R := by
      exact
        (zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral_eq
          g F T R).symm

/-- If the square-punctured rectangle boundary vanishes, the isolated `s = 1`
standard boundary equals the inner square boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardBoundary_eq_innerSquare_of_squarePunctured_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) (R : ℝ)
    (hcauchy :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R = 0) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F T =
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        R := by
  let S : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T
  let I : ℂ :=
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      R
  have hsub : S - I = 0 := by
    calc
      S - I =
          zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            F T R := by
        exact
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardBoundary_sub_innerSquare_eq_squarePunctured
            f F hT R
      _ = 0 := hcauchy
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F T = S := by
      rfl
    _ = (S - I) + I := by
      exact (sub_add_cancel S I).symm
    _ = 0 + I := by
      exact congrArg (fun z : ℂ => z + I) hsub
    _ =
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        R := by
      exact zero_add I

/-- If each of the four rectangular cells in the one-pole punctured rectangle
has zero boundary integral, then the named four-cell boundary sum is zero. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cells
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R = 0)
    (htop :
      zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R = 0)
    (hleft :
      zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R = 0)
    (hright :
      zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R = 0) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R = 0 := by
  let B : ℂ := zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R
  let U : ℂ := zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R
  let L : ℂ := zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R
  let Q : ℂ := zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R
  calc
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
        B + U + L + Q := by
      rfl
    _ = 0 + U + L + Q := by
      exact congrArg (fun z : ℂ => z + U + L + Q) hbottom
    _ = 0 + 0 + L + Q := by
      exact congrArg (fun z : ℂ => 0 + z + L + Q) htop
    _ = 0 + 0 + 0 + Q := by
      exact congrArg (fun z : ℂ => 0 + 0 + z + Q) hleft
    _ = 0 + 0 + 0 + 0 := by
      exact congrArg (fun z : ℂ => 0 + 0 + 0 + z) hright
    _ = 0 := by
      calc
        0 + 0 + 0 + (0 : ℂ) = (0 + 0 + 0 : ℂ) := by
          exact add_zero (0 + 0 + 0 : ℂ)
        _ = (0 + 0 : ℂ) := by
          exact add_zero (0 + 0 : ℂ)
        _ = (0 : ℂ) := by
          exact add_zero (0 : ℂ)

/-- The bottom puncture cell has zero boundary under the rectangular
Cauchy-Goursat hypotheses on that cell. -/
theorem zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral_eq_zero_of_cauchy
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (s : Set ℂ) (hs : s.Countable)
    (Hc :
      ContinuousOn g
        ([[ ((1 - F.c) + (-T) * Complex.I).re,
             (F.c + (-R) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-T) * Complex.I).im,
             (F.c + (-R) * Complex.I).im ]]))
    (Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re)
                (max ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im)
                (max ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im) \ s →
          DifferentiableAt ℂ g x) :
    zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R = 0 := by
  exact
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
      g ((1 - F.c) + (-T) * Complex.I) (F.c + (-R) * Complex.I)
      s hs Hc Hd

/-- The top puncture cell has zero boundary under the rectangular
Cauchy-Goursat hypotheses on that cell. -/
theorem zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral_eq_zero_of_cauchy
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (s : Set ℂ) (hs : s.Countable)
    (Hc :
      ContinuousOn g
        ([[ ((1 - F.c) + R * Complex.I).re,
             (F.c + T * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + R * Complex.I).im,
             (F.c + T * Complex.I).im ]]))
    (Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re)
                (max ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im)
                (max ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im) \ s →
          DifferentiableAt ℂ g x) :
    zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R = 0 := by
  exact
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
      g ((1 - F.c) + R * Complex.I) (F.c + T * Complex.I)
      s hs Hc Hd

/-- The left puncture cell has zero boundary under the rectangular
Cauchy-Goursat hypotheses on that cell. -/
theorem zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral_eq_zero_of_cauchy
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (s : Set ℂ) (hs : s.Countable)
    (Hc :
      ContinuousOn g
        ([[ ((1 - F.c) + (-R) * Complex.I).re,
             ((1 - R) + R * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-R) * Complex.I).im,
             ((1 - R) + R * Complex.I).im ]]))
    (Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).re
                  ((1 - R) + R * Complex.I).re)
                (max ((1 - F.c) + (-R) * Complex.I).re
                  ((1 - R) + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).im
                  ((1 - R) + R * Complex.I).im)
                (max ((1 - F.c) + (-R) * Complex.I).im
                  ((1 - R) + R * Complex.I).im) \ s →
          DifferentiableAt ℂ g x) :
    zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R = 0 := by
  exact
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
      g ((1 - F.c) + (-R) * Complex.I) ((1 - R) + R * Complex.I)
      s hs Hc Hd

/-- The right puncture cell has zero boundary under the rectangular
Cauchy-Goursat hypotheses on that cell. -/
theorem zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral_eq_zero_of_cauchy
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (s : Set ℂ) (hs : s.Countable)
    (Hc :
      ContinuousOn g
        ([[ ((1 + R) + (-R) * Complex.I).re,
             (F.c + R * Complex.I).re ]] ×ℂ
          [[ ((1 + R) + (-R) * Complex.I).im,
             (F.c + R * Complex.I).im ]]))
    (Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 + R) + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re)
                (max ((1 + R) + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 + R) + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im)
                (max ((1 + R) + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im) \ s →
          DifferentiableAt ℂ g x) :
    zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R = 0 := by
  exact
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
      g ((1 + R) + (-R) * Complex.I) (F.c + R * Complex.I)
      s hs Hc Hd

/-- The finite four-cell boundary sum vanishes when each of the four cells
satisfies Cauchy-Goursat. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cauchy
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (sBottom sTop sLeft sRight : Set ℂ)
    (hsBottom : sBottom.Countable)
    (hsTop : sTop.Countable)
    (hsLeft : sLeft.Countable)
    (hsRight : sRight.Countable)
    (HcBottom :
      ContinuousOn g
        ([[ ((1 - F.c) + (-T) * Complex.I).re,
             (F.c + (-R) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-T) * Complex.I).im,
             (F.c + (-R) * Complex.I).im ]]))
    (HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re)
                (max ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im)
                (max ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im) \ sBottom →
          DifferentiableAt ℂ g x)
    (HcTop :
      ContinuousOn g
        ([[ ((1 - F.c) + R * Complex.I).re,
             (F.c + T * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + R * Complex.I).im,
             (F.c + T * Complex.I).im ]]))
    (HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re)
                (max ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im)
                (max ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im) \ sTop →
          DifferentiableAt ℂ g x)
    (HcLeft :
      ContinuousOn g
        ([[ ((1 - F.c) + (-R) * Complex.I).re,
             ((1 - R) + R * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-R) * Complex.I).im,
             ((1 - R) + R * Complex.I).im ]]))
    (HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).re
                  ((1 - R) + R * Complex.I).re)
                (max ((1 - F.c) + (-R) * Complex.I).re
                  ((1 - R) + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).im
                  ((1 - R) + R * Complex.I).im)
                (max ((1 - F.c) + (-R) * Complex.I).im
                  ((1 - R) + R * Complex.I).im) \ sLeft →
          DifferentiableAt ℂ g x)
    (HcRight :
      ContinuousOn g
        ([[ ((1 + R) + (-R) * Complex.I).re,
             (F.c + R * Complex.I).re ]] ×ℂ
          [[ ((1 + R) + (-R) * Complex.I).im,
             (F.c + R * Complex.I).im ]]))
    (HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 + R) + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re)
                (max ((1 + R) + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 + R) + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im)
                (max ((1 + R) + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im) \ sRight →
          DifferentiableAt ℂ g x) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R = 0 := by
  have hbottom :
      zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral g F T R = 0 :=
    zetaExplicitFormulaOnePoleBottomPunctureCellBoundaryIntegral_eq_zero_of_cauchy
      g F T R sBottom hsBottom HcBottom HdBottom
  have htop :
      zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral g F T R = 0 :=
    zetaExplicitFormulaOnePoleTopPunctureCellBoundaryIntegral_eq_zero_of_cauchy
      g F T R sTop hsTop HcTop HdTop
  have hleft :
      zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral g F T R = 0 :=
    zetaExplicitFormulaOnePoleLeftPunctureCellBoundaryIntegral_eq_zero_of_cauchy
      g F T R sLeft hsLeft HcLeft HdLeft
  have hright :
      zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral g F T R = 0 :=
    zetaExplicitFormulaOnePoleRightPunctureCellBoundaryIntegral_eq_zero_of_cauchy
      g F T R sRight hsRight HcRight HdRight
  exact
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cells
      g F T R hbottom htop hleft hright

/-- The canonical one-pole puncture radius: half of the smallest horizontal
and vertical margin from the pole `1` to the rectangle boundary. -/
noncomputable def zetaExplicitFormulaOnePolePunctureRadius
    (F : ExplicitFormulaContourFamily) (T : ℝ) : ℝ :=
  min (min (F.c - 1) F.c) T / 2

/-- The one-pole puncture radius is positive at positive height. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_pos
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    0 < zetaExplicitFormulaOnePolePunctureRadius F T := by
  have hright : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hleft : 0 < F.c :=
    F.c_pos
  have hhorizontal : 0 < min (F.c - 1) F.c :=
    lt_min hright hleft
  have hall : 0 < min (min (F.c - 1) F.c) T :=
    lt_min hhorizontal hT
  exact half_pos hall

/-- The one-pole puncture radius is bounded by the right horizontal margin. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_lt_rightMargin
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaOnePolePunctureRadius F T < F.c - 1 := by
  have hpos : 0 < zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePolePunctureRadius_pos F hT
  have hmin_le : min (min (F.c - 1) F.c) T ≤ F.c - 1 :=
    le_trans (min_le_left (min (F.c - 1) F.c) T)
      (min_le_left (F.c - 1) F.c)
  have hhalf_le :
      zetaExplicitFormulaOnePolePunctureRadius F T ≤ (F.c - 1) / 2 := by
    exact div_le_div_of_nonneg_right hmin_le (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hmargin_pos : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hhalf_lt : (F.c - 1) / 2 < F.c - 1 := by
    calc
      (F.c - 1) / 2 < (F.c - 1) / 1 := by
        exact div_lt_div_of_pos_left hmargin_pos zero_lt_one one_lt_two
      _ = F.c - 1 := by
        exact div_one (F.c - 1)
  exact lt_of_le_of_lt hhalf_le hhalf_lt

/-- The one-pole puncture radius is bounded by the left horizontal margin. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_lt_leftMargin
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaOnePolePunctureRadius F T < F.c := by
  have hmin_le : min (min (F.c - 1) F.c) T ≤ F.c :=
    le_trans (min_le_left (min (F.c - 1) F.c) T)
      (min_le_right (F.c - 1) F.c)
  have hhalf_le :
      zetaExplicitFormulaOnePolePunctureRadius F T ≤ F.c / 2 := by
    exact div_le_div_of_nonneg_right hmin_le (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hmargin_pos : 0 < F.c :=
    F.c_pos
  have hhalf_lt : F.c / 2 < F.c := by
    calc
      F.c / 2 < F.c / 1 := by
        exact div_lt_div_of_pos_left hmargin_pos zero_lt_one one_lt_two
      _ = F.c := by
        exact div_one F.c
  exact lt_of_le_of_lt hhalf_le hhalf_lt

/-- The one-pole puncture radius is bounded by the vertical height. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_lt_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaOnePolePunctureRadius F T < T := by
  have hmin_le : min (min (F.c - 1) F.c) T ≤ T :=
    min_le_right (min (F.c - 1) F.c) T
  have hhalf_le :
      zetaExplicitFormulaOnePolePunctureRadius F T ≤ T / 2 := by
    exact div_le_div_of_nonneg_right hmin_le (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hhalf_lt : T / 2 < T := by
    calc
      T / 2 < T / 1 := by
        exact div_lt_div_of_pos_left hT zero_lt_one one_lt_two
      _ = T := by
        exact div_one T
  exact lt_of_le_of_lt hhalf_le hhalf_lt

/-- A complex norm bound around `1` controls the real-coordinate displacement
from the pole. -/
theorem zetaExplicitFormulaOnePole_abs_re_sub_one_lt_of_norm_lt
    {z : ℂ} {r : ℝ} (hz : ‖z - 1‖ < r) :
    |(z - 1).re| < r := by
  have hre_le_abs :
      |(z - 1).re| ≤ Complex.abs (z - 1) :=
    Complex.abs_re_le_abs (z - 1)
  have habs_norm :
      Complex.abs (z - 1) = ‖z - 1‖ :=
    (Complex.norm_eq_abs (z - 1)).symm
  have hre_le_norm :
      |(z - 1).re| ≤ ‖z - 1‖ := by
    exact Eq.subst
      (motive := fun a : ℝ => |(z - 1).re| ≤ a)
      habs_norm
      hre_le_abs
  exact lt_of_le_of_lt hre_le_norm hz

/-- A complex norm bound around `1` controls the imaginary-coordinate
displacement from the pole. -/
theorem zetaExplicitFormulaOnePole_abs_im_lt_of_norm_lt
    {z : ℂ} {r : ℝ} (hz : ‖z - 1‖ < r) :
    |(z - 1).im| < r := by
  have him_le_abs :
      |(z - 1).im| ≤ Complex.abs (z - 1) :=
    Complex.abs_im_le_abs (z - 1)
  have habs_norm :
      Complex.abs (z - 1) = ‖z - 1‖ :=
    (Complex.norm_eq_abs (z - 1)).symm
  have him_le_norm :
      |(z - 1).im| ≤ ‖z - 1‖ := by
    exact Eq.subst
      (motive := fun a : ℝ => |(z - 1).im| ≤ a)
      habs_norm
      him_le_abs
  exact lt_of_le_of_lt him_le_norm hz

/-- A non-strict complex norm bound around `1` controls the real-coordinate
displacement from the pole. -/
theorem zetaExplicitFormulaOnePole_abs_re_sub_one_le_of_norm_le
    {z : ℂ} {r : ℝ} (hz : ‖z - 1‖ ≤ r) :
    |(z - 1).re| ≤ r := by
  have hre_le_abs :
      |(z - 1).re| ≤ Complex.abs (z - 1) :=
    Complex.abs_re_le_abs (z - 1)
  have habs_norm :
      Complex.abs (z - 1) = ‖z - 1‖ :=
    (Complex.norm_eq_abs (z - 1)).symm
  have hre_le_norm :
      |(z - 1).re| ≤ ‖z - 1‖ := by
    exact Eq.subst
      (motive := fun a : ℝ => |(z - 1).re| ≤ a)
      habs_norm
      hre_le_abs
  exact le_trans hre_le_norm hz

/-- A non-strict complex norm bound around `1` controls the imaginary-coordinate
displacement from the pole. -/
theorem zetaExplicitFormulaOnePole_abs_im_le_of_norm_le
    {z : ℂ} {r : ℝ} (hz : ‖z - 1‖ ≤ r) :
    |(z - 1).im| ≤ r := by
  have him_le_abs :
      |(z - 1).im| ≤ Complex.abs (z - 1) :=
    Complex.abs_im_le_abs (z - 1)
  have habs_norm :
      Complex.abs (z - 1) = ‖z - 1‖ :=
    (Complex.norm_eq_abs (z - 1)).symm
  have him_le_norm :
      |(z - 1).im| ≤ ‖z - 1‖ := by
    exact Eq.subst
      (motive := fun a : ℝ => |(z - 1).im| ≤ a)
      habs_norm
      him_le_abs
  exact le_trans him_le_norm hz

/-- A point within the one-pole puncture radius lies strictly below the right
vertical edge. -/
theorem zetaExplicitFormulaOnePole_re_lt_rightEdge_of_norm_lt_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ < zetaExplicitFormulaOnePolePunctureRadius F T) :
    z.re < F.c := by
  have hre_abs :
      |(z - 1).re| <
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_re_sub_one_lt_of_norm_lt hz
  have hre_lt_radius :
      (z - 1).re <
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    (abs_lt.mp hre_abs).2
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < F.c - 1 :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_rightMargin F hT
  have hre_sub_lt :
      (z - 1).re < F.c - 1 :=
    lt_trans hre_lt_radius hradius_lt
  have hre_eq :
      (z - 1).re = z.re - 1 := by
    exact Complex.sub_re z 1
  have hz_re_sub_lt :
      z.re - 1 < F.c - 1 :=
    Eq.subst
      (motive := fun x : ℝ => x < F.c - 1)
      hre_eq
      hre_sub_lt
  exact (sub_lt_sub_iff_right (1 : ℝ)).mp hz_re_sub_lt

/-- A point within the one-pole puncture radius lies strictly above the left
vertical edge. -/
theorem zetaExplicitFormulaOnePole_leftEdge_lt_re_of_norm_lt_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ < zetaExplicitFormulaOnePolePunctureRadius F T) :
    1 - F.c < z.re := by
  have hre_abs :
      |(z - 1).re| <
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_re_sub_one_lt_of_norm_lt hz
  have hneg_radius_lt_re :
      -zetaExplicitFormulaOnePolePunctureRadius F T <
        (z - 1).re :=
    (abs_lt.mp hre_abs).1
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < F.c :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_leftMargin F hT
  have hneg_margin_lt_neg_radius :
      -F.c < -zetaExplicitFormulaOnePolePunctureRadius F T :=
    neg_lt_neg hradius_lt
  have hneg_margin_lt_re_sub :
      -F.c < (z - 1).re :=
    lt_trans hneg_margin_lt_neg_radius hneg_radius_lt_re
  have hre_eq :
      (z - 1).re = z.re - 1 := by
    exact Complex.sub_re z 1
  have hneg_margin_lt_z_sub :
      -F.c < z.re - 1 :=
    Eq.subst
      (motive := fun x : ℝ => -F.c < x)
      hre_eq
      hneg_margin_lt_re_sub
  have hshifted :
      -F.c + 1 < z.re :=
    (lt_sub_iff_add_lt).mp hneg_margin_lt_z_sub
  have hleft_eq :
      1 - F.c = -F.c + 1 := by
    calc
      1 - F.c = 1 + -F.c := by
        exact sub_eq_add_neg 1 F.c
      _ = -F.c + 1 := by
        exact add_comm 1 (-F.c)
  exact Eq.subst
    (motive := fun x : ℝ => x < z.re)
    hleft_eq.symm
    hshifted

/-- A point within the one-pole puncture radius lies below the upper horizontal
edge. -/
theorem zetaExplicitFormulaOnePole_im_lt_height_of_norm_lt_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ < zetaExplicitFormulaOnePolePunctureRadius F T) :
    z.im < T := by
  have him_abs :
      |(z - 1).im| <
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_im_lt_of_norm_lt hz
  have him_lt_radius :
      (z - 1).im <
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    (abs_lt.mp him_abs).2
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < T :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_height F hT
  have him_sub_lt :
      (z - 1).im < T :=
    lt_trans him_lt_radius hradius_lt
  have him_eq :
      (z - 1).im = z.im := by
    calc
      (z - 1).im = z.im - (1 : ℂ).im := by
        exact Complex.sub_im z 1
      _ = z.im - 0 := by
        exact congrArg (fun y : ℝ => z.im - y) Complex.one_im
      _ = z.im := by
        exact sub_zero z.im
  exact Eq.subst
    (motive := fun x : ℝ => x < T)
    him_eq
    him_sub_lt

/-- A point within the one-pole puncture radius lies above the lower horizontal
edge. -/
theorem zetaExplicitFormulaOnePole_neg_height_lt_im_of_norm_lt_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ < zetaExplicitFormulaOnePolePunctureRadius F T) :
    -T < z.im := by
  have him_abs :
      |(z - 1).im| <
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_im_lt_of_norm_lt hz
  have hneg_radius_lt_im :
      -zetaExplicitFormulaOnePolePunctureRadius F T <
        (z - 1).im :=
    (abs_lt.mp him_abs).1
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < T :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_height F hT
  have hneg_T_lt_neg_radius :
      -T < -zetaExplicitFormulaOnePolePunctureRadius F T :=
    neg_lt_neg hradius_lt
  have hneg_T_lt_im_sub :
      -T < (z - 1).im :=
    lt_trans hneg_T_lt_neg_radius hneg_radius_lt_im
  have him_eq :
      (z - 1).im = z.im := by
    calc
      (z - 1).im = z.im - (1 : ℂ).im := by
        exact Complex.sub_im z 1
      _ = z.im - 0 := by
        exact congrArg (fun y : ℝ => z.im - y) Complex.one_im
      _ = z.im := by
        exact sub_zero z.im
  exact Eq.subst
    (motive := fun x : ℝ => -T < x)
    him_eq
    hneg_T_lt_im_sub

/-- A point in the closed one-pole puncture disk lies strictly below the right
vertical edge. -/
theorem zetaExplicitFormulaOnePole_re_lt_rightEdge_of_norm_le_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ ≤ zetaExplicitFormulaOnePolePunctureRadius F T) :
    z.re < F.c := by
  have hre_abs :
      |(z - 1).re| ≤
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_re_sub_one_le_of_norm_le hz
  have hre_le_radius :
      (z - 1).re ≤
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    (abs_le.mp hre_abs).2
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < F.c - 1 :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_rightMargin F hT
  have hre_sub_lt :
      (z - 1).re < F.c - 1 :=
    lt_of_le_of_lt hre_le_radius hradius_lt
  have hre_eq :
      (z - 1).re = z.re - 1 := by
    exact Complex.sub_re z 1
  have hz_re_sub_lt :
      z.re - 1 < F.c - 1 :=
    Eq.subst
      (motive := fun x : ℝ => x < F.c - 1)
      hre_eq
      hre_sub_lt
  exact (sub_lt_sub_iff_right (1 : ℝ)).mp hz_re_sub_lt

/-- A point in the closed one-pole puncture disk lies strictly above the left
vertical edge. -/
theorem zetaExplicitFormulaOnePole_leftEdge_lt_re_of_norm_le_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ ≤ zetaExplicitFormulaOnePolePunctureRadius F T) :
    1 - F.c < z.re := by
  have hre_abs :
      |(z - 1).re| ≤
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_re_sub_one_le_of_norm_le hz
  have hneg_radius_le_re :
      -zetaExplicitFormulaOnePolePunctureRadius F T ≤
        (z - 1).re :=
    (abs_le.mp hre_abs).1
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < F.c :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_leftMargin F hT
  have hneg_margin_lt_neg_radius :
      -F.c < -zetaExplicitFormulaOnePolePunctureRadius F T :=
    neg_lt_neg hradius_lt
  have hneg_margin_lt_re_sub :
      -F.c < (z - 1).re :=
    lt_of_lt_of_le hneg_margin_lt_neg_radius hneg_radius_le_re
  have hre_eq :
      (z - 1).re = z.re - 1 := by
    exact Complex.sub_re z 1
  have hneg_margin_lt_z_sub :
      -F.c < z.re - 1 :=
    Eq.subst
      (motive := fun x : ℝ => -F.c < x)
      hre_eq
      hneg_margin_lt_re_sub
  have hshifted :
      -F.c + 1 < z.re :=
    (lt_sub_iff_add_lt).mp hneg_margin_lt_z_sub
  have hleft_eq :
      1 - F.c = -F.c + 1 := by
    calc
      1 - F.c = 1 + -F.c := by
        exact sub_eq_add_neg 1 F.c
      _ = -F.c + 1 := by
        exact add_comm 1 (-F.c)
  exact Eq.subst
    (motive := fun x : ℝ => x < z.re)
    hleft_eq.symm
    hshifted

/-- A point in the closed one-pole puncture disk lies below the upper
horizontal edge. -/
theorem zetaExplicitFormulaOnePole_im_lt_height_of_norm_le_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ ≤ zetaExplicitFormulaOnePolePunctureRadius F T) :
    z.im < T := by
  have him_abs :
      |(z - 1).im| ≤
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_im_le_of_norm_le hz
  have him_le_radius :
      (z - 1).im ≤
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    (abs_le.mp him_abs).2
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < T :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_height F hT
  have him_sub_lt :
      (z - 1).im < T :=
    lt_of_le_of_lt him_le_radius hradius_lt
  have him_eq :
      (z - 1).im = z.im := by
    calc
      (z - 1).im = z.im - (1 : ℂ).im := by
        exact Complex.sub_im z 1
      _ = z.im - 0 := by
        exact congrArg (fun y : ℝ => z.im - y) Complex.one_im
      _ = z.im := by
        exact sub_zero z.im
  exact Eq.subst
    (motive := fun x : ℝ => x < T)
    him_eq
    him_sub_lt

/-- A point in the closed one-pole puncture disk lies above the lower horizontal
edge. -/
theorem zetaExplicitFormulaOnePole_neg_height_lt_im_of_norm_le_radius
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    {z : ℂ}
    (hz :
      ‖z - 1‖ ≤ zetaExplicitFormulaOnePolePunctureRadius F T) :
    -T < z.im := by
  have him_abs :
      |(z - 1).im| ≤
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaExplicitFormulaOnePole_abs_im_le_of_norm_le hz
  have hneg_radius_le_im :
      -zetaExplicitFormulaOnePolePunctureRadius F T ≤
        (z - 1).im :=
    (abs_le.mp him_abs).1
  have hradius_lt :
      zetaExplicitFormulaOnePolePunctureRadius F T < T :=
    zetaExplicitFormulaOnePolePunctureRadius_lt_height F hT
  have hneg_T_lt_neg_radius :
      -T < -zetaExplicitFormulaOnePolePunctureRadius F T :=
    neg_lt_neg hradius_lt
  have hneg_T_lt_im_sub :
      -T < (z - 1).im :=
    lt_of_lt_of_le hneg_T_lt_neg_radius hneg_radius_le_im
  have him_eq :
      (z - 1).im = z.im := by
    calc
      (z - 1).im = z.im - (1 : ℂ).im := by
        exact Complex.sub_im z 1
      _ = z.im - 0 := by
        exact congrArg (fun y : ℝ => z.im - y) Complex.one_im
      _ = z.im := by
        exact sub_zero z.im
  exact Eq.subst
    (motive := fun x : ℝ => -T < x)
    him_eq
    hneg_T_lt_im_sub

/-- The canonical one-pole puncture disk is contained in the open finite
rectangle interior at positive height. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_ball_subset_interior
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    Metric.ball (1 : ℂ) (zetaExplicitFormulaOnePolePunctureRadius F T) ⊆
      explicitFormulaContourFamilyInterior F T := by
  intro z hzball
  have hdist :
      dist z (1 : ℂ) <
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    hzball
  have hnorm :
      ‖z - 1‖ <
        zetaExplicitFormulaOnePolePunctureRadius F T := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        x < zetaExplicitFormulaOnePolePunctureRadius F T)
      (dist_eq_norm z (1 : ℂ))
      hdist
  have hleft :
      1 - F.c < z.re :=
    zetaExplicitFormulaOnePole_leftEdge_lt_re_of_norm_lt_radius F hT hnorm
  have hright :
      z.re < F.c :=
    zetaExplicitFormulaOnePole_re_lt_rightEdge_of_norm_lt_radius F hT hnorm
  have hre :
      z.re ∈ Set.uIoo F.c (1 - F.c) :=
    Set.mem_uIoo_of_gt hleft hright
  have him_lower :
      -T < z.im :=
    zetaExplicitFormulaOnePole_neg_height_lt_im_of_norm_lt_radius F hT hnorm
  have him_upper :
      z.im < T :=
    zetaExplicitFormulaOnePole_im_lt_height_of_norm_lt_radius F hT hnorm
  have him :
      z.im ∈ Set.Ioo (-T) T :=
    And.intro him_lower him_upper
  exact And.intro hre him

/-- The closed canonical one-pole puncture disk is contained in the open finite
rectangle interior at positive height.  This is the geometric radius choice
needed for the finite punctured-rectangle Cauchy construction. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_closedBall_subset_interior
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    Metric.closedBall (1 : ℂ) (zetaExplicitFormulaOnePolePunctureRadius F T) ⊆
      explicitFormulaContourFamilyInterior F T := by
  intro z hzball
  have hdist :
      dist z (1 : ℂ) ≤
        zetaExplicitFormulaOnePolePunctureRadius F T :=
    hzball
  have hnorm :
      ‖z - 1‖ ≤
        zetaExplicitFormulaOnePolePunctureRadius F T := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ zetaExplicitFormulaOnePolePunctureRadius F T)
      (dist_eq_norm z (1 : ℂ))
      hdist
  have hleft :
      1 - F.c < z.re :=
    zetaExplicitFormulaOnePole_leftEdge_lt_re_of_norm_le_radius F hT hnorm
  have hright :
      z.re < F.c :=
    zetaExplicitFormulaOnePole_re_lt_rightEdge_of_norm_le_radius F hT hnorm
  have hre :
      z.re ∈ Set.uIoo F.c (1 - F.c) :=
    Set.mem_uIoo_of_gt hleft hright
  have him_lower :
      -T < z.im :=
    zetaExplicitFormulaOnePole_neg_height_lt_im_of_norm_le_radius F hT hnorm
  have him_upper :
      z.im < T :=
    zetaExplicitFormulaOnePole_im_lt_height_of_norm_le_radius F hT hnorm
  have him :
      z.im ∈ Set.Ioo (-T) T :=
    And.intro him_lower him_upper
  exact And.intro hre him

/-- At positive height there is an explicit finite one-pole puncture radius
whose closed disk stays inside the contour rectangle. -/
theorem zetaExplicitFormulaOnePole_exists_positive_punctureRadius_closedBall_subset_interior
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∃ R : ℝ,
      0 < R ∧
        Metric.closedBall (1 : ℂ) R ⊆
          explicitFormulaContourFamilyInterior F T := by
  exact
    Exists.intro
      (zetaExplicitFormulaOnePolePunctureRadius F T)
      (And.intro
        (zetaExplicitFormulaOnePolePunctureRadius_pos F hT)
        (zetaExplicitFormulaOnePolePunctureRadius_closedBall_subset_interior
          F hT))

/-- A boundary point of a finite explicit-formula rectangle is not an interior
point. -/
theorem explicitFormulaContourFamilyBoundary_not_mem_interior
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    z ∉ explicitFormulaContourFamilyInterior F T := by
  intro hinterior
  have hspan :
      1 - F.c < F.c :=
    lt_trans F.one_sub_c_neg F.c_pos
  have hre_open :
      z.re ∈ Set.Ioo (1 - F.c) F.c := by
    have hu :
        z.re ∈ Set.uIoo F.c (1 - F.c) :=
      hinterior.1
    have hu_eq :
        Set.uIoo F.c (1 - F.c) = Set.Ioo (1 - F.c) F.c :=
      Set.uIoo_of_gt hspan
    exact Eq.subst
      (motive := fun s : Set ℝ => z.re ∈ s)
      hu_eq
      hu
  match hboundary with
  | Or.inl hright =>
      match hright with
      | ⟨t, ht, hzpath⟩ =>
          have hz_re :
              z.re = F.c := by
            calc
              z.re = (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re := by
                exact congrArg Complex.re hzpath
              _ = (F.rectangle T).c := by
                exact zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
              _ = F.c := by
                exact ExplicitFormulaContourFamily.rectangle_c F T
          have hright_lt :
              z.re < F.c :=
            hre_open.2
          have hfalse :
              F.c < F.c :=
            Eq.subst
              (motive := fun x : ℝ => x < F.c)
              hz_re
              hright_lt
          exact (lt_irrefl F.c) hfalse
  | Or.inr (Or.inl hleft) =>
      match hleft with
      | ⟨t, ht, hzpath⟩ =>
          have hz_re :
              z.re = 1 - F.c := by
            calc
              z.re = (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re := by
                exact congrArg Complex.re hzpath
              _ = 1 - (F.rectangle T).c := by
                exact zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
              _ = 1 - F.c := by
                exact congrArg (fun x : ℝ => 1 - x)
                  (ExplicitFormulaContourFamily.rectangle_c F T)
          have hleft_lt :
              1 - F.c < z.re :=
            hre_open.1
          have hfalse :
              1 - F.c < 1 - F.c :=
            Eq.subst
              (motive := fun x : ℝ => 1 - F.c < x)
              hz_re
              hleft_lt
          exact (lt_irrefl (1 - F.c)) hfalse
  | Or.inr (Or.inr (Or.inl htop)) =>
      match htop with
      | ⟨x, hx, hzpath⟩ =>
          have hz_im :
              z.im = T := by
            calc
              z.im = (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im := by
                exact congrArg Complex.im hzpath
              _ = (F.rectangle T).T := by
                exact zetaCompletedExplicitFormulaTopPath_im (F.rectangle T) x
              _ = T := by
                rfl
          have him_lt :
              z.im < T :=
            hinterior.2.2
          have hfalse :
              T < T :=
            Eq.subst
              (motive := fun y : ℝ => y < T)
              hz_im
              him_lt
          exact (lt_irrefl T) hfalse
  | Or.inr (Or.inr (Or.inr hbottom)) =>
      match hbottom with
      | ⟨x, hx, hzpath⟩ =>
          have hz_im :
              z.im = -T := by
            calc
              z.im = (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im := by
                exact congrArg Complex.im hzpath
              _ = -(F.rectangle T).T := by
                exact zetaCompletedExplicitFormulaBottomPath_im (F.rectangle T) x
              _ = -T := by
                rfl
          have him_lt :
              -T < z.im :=
            hinterior.2.1
          have hfalse :
              -T < -T :=
            Eq.subst
              (motive := fun y : ℝ => -T < y)
              hz_im
              him_lt
          exact (lt_irrefl (-T)) hfalse

/-- The canonical one-pole puncture closed disk is disjoint from the rectangle
boundary. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_closedBall_disjoint_boundary
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    Disjoint
      (Metric.closedBall (1 : ℂ) (zetaExplicitFormulaOnePolePunctureRadius F T))
      (explicitFormulaContourFamilyBoundary F T) := by
  refine Set.disjoint_left.mpr ?_
  intro z hzclosed hzboundary
  have hinterior :
      z ∈ explicitFormulaContourFamilyInterior F T :=
    zetaExplicitFormulaOnePolePunctureRadius_closedBall_subset_interior
      F hT hzclosed
  exact
    explicitFormulaContourFamilyBoundary_not_mem_interior
      F T hzboundary hinterior

/-- The canonical one-pole puncture circle is disjoint from the rectangle
boundary. -/
theorem zetaExplicitFormulaOnePolePunctureRadius_sphere_disjoint_boundary
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    Disjoint
      (Metric.sphere (1 : ℂ) (zetaExplicitFormulaOnePolePunctureRadius F T))
      (explicitFormulaContourFamilyBoundary F T) := by
  refine Set.disjoint_left.mpr ?_
  intro z hzsphere hzboundary
  have hzclosed :
      z ∈
        Metric.closedBall (1 : ℂ)
          (zetaExplicitFormulaOnePolePunctureRadius F T) := by
    exact Metric.mem_closedBall.mpr (le_of_eq hzsphere)
  have hdisjoint :
      Disjoint
        (Metric.closedBall (1 : ℂ)
          (zetaExplicitFormulaOnePolePunctureRadius F T))
        (explicitFormulaContourFamilyBoundary F T) :=
    zetaExplicitFormulaOnePolePunctureRadius_closedBall_disjoint_boundary
      F hT
  exact Set.disjoint_left.mp hdisjoint hzclosed hzboundary

/-- Algebraic residue cancellation for the isolated `s = 1` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_localResidue_algebra
    (z φ : ℂ) (hz : z - 1 ≠ 0) :
    (z - 1) * ((-1 / (z - 1)) * φ) = -φ := by
  have hdiv_neg :
      -1 / (z - 1) = -(1 / (z - 1)) :=
    neg_div (z - 1) (1 : ℂ)
  have hcoeff :
      (z - 1) * (-1 / (z - 1)) = -1 := by
    calc
      (z - 1) * (-1 / (z - 1)) =
      (z - 1) * (-(1 / (z - 1))) := by
        exact congrArg (fun a : ℂ => (z - 1) * a) hdiv_neg
      _ = -((z - 1) * (1 / (z - 1))) := by
        exact mul_neg (z - 1) (1 / (z - 1))
      _ = -((z - 1) * ((z - 1)⁻¹)) := by
        have hone_div : 1 / (z - 1) = ((z - 1)⁻¹) := by
          exact one_div (z - 1)
        exact congrArg
          (fun a : ℂ => -((z - 1) * a))
          hone_div
      _ = -1 := by
        exact congrArg Neg.neg (mul_inv_cancel₀ hz)
  calc
    (z - 1) * ((-1 / (z - 1)) * φ) =
        ((z - 1) * (-1 / (z - 1))) * φ := by
      exact (mul_assoc (z - 1) (-1 / (z - 1)) φ).symm
    _ = (-1) * φ := by
      exact congrArg (fun a : ℂ => a * φ) hcoeff
    _ = -φ := by
      exact neg_one_mul φ

/-- Local residue of the isolated `s = 1` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_localResidue_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ =>
        (z - 1) *
          ((-1 / (z - 1)) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 / 2))) := by
  have hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f (1 - 1 / 2))) := by
    have hcontinuous :
        ContinuousAt
          (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (1 : ℂ) :=
      (zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi (1 : ℂ)).continuousAt
    exact hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have htarget_arg : (1 : ℂ) - 1 / 2 = 1 / 2 := by
    exact sub_half (1 : ℂ)
  have hneg :
      Tendsto
        (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 - 1 / 2))) :=
    hphi.neg
  have hpointwise :
      (fun z : ℂ =>
        (z - 1) *
          ((-1 / (z - 1)) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2))) =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) := by
    exact
      eventually_nhdsWithin_of_forall
        (fun z hz_ne =>
          zetaCompletedExplicitFormulaCorrectionOnePole_localResidue_algebra
            z
            (zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
            (sub_ne_zero.mpr hz_ne))
  have hraw :
      Tendsto
        (fun z : ℂ =>
          (z - 1) *
            ((-1 / (z - 1)) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 - 1 / 2))) :=
    Tendsto.congr' hpointwise.symm hneg
  exact Eq.subst
    (motive := fun w : ℂ =>
      Tendsto
        (fun z : ℂ =>
          (z - 1) *
            ((-1 / (z - 1)) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f w)))
    htarget_arg
    hraw

/-- Local residue of the named isolated `s = 1` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_localResidue_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ =>
        (z - 1) *
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 / 2))) := by
  exact zetaCompletedExplicitFormulaCorrectionOnePole_localResidue_tendsto f hPhi

/-- Deleted-circle residue theorem for the isolated `s = 1` correction kernel,
with the corrected local residue `-Phi(1/2)`. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_deletedCircleIntegral_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ =>
          (z - 1) *
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Metric.closedBall (1 : ℂ) R \ {(1 : ℂ)}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) R \ {(1 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (w - 1) *
                zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z) :
    (∮ z in C((1 : ℂ), R),
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  exact
    zetaExplicitFormulaSinglePole_deletedCircleIntegral_eq_twoPiI_smul_residue
      hR
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))
      s
      hs
      hcontinuous
      hdifferentiable
      (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_localResidue_tendsto
        f hPhi)

/-- The isolated `s = 1` correction kernel is differentiable away from its pole. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_differentiableAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z - 1 ≠ 0) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        (-1 / (w - 1)) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      z := by
  have hden :
      DifferentiableAt ℂ (fun w : ℂ => w - 1) z :=
    differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
  have hcoeff :
      DifferentiableAt ℂ (fun w : ℂ => -1 / (w - 1)) z :=
    (differentiableAt_const (-(1 : ℂ))).div hden hz
  have hshift :
      DifferentiableAt ℂ
        (fun w : ℂ => zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z :=
    zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi z
  exact hcoeff.mul hshift

/-- The isolated `s = 1` correction kernel is continuous away from its pole. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_continuousAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z - 1 ≠ 0) :
    ContinuousAt
      (fun w : ℂ =>
        (-1 / (w - 1)) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      z :=
  (zetaCompletedExplicitFormulaCorrectionOnePole_differentiableAt_off_pole
    f hPhi hz).continuousAt

/-- The named isolated `s = 1` correction kernel is differentiable away from
its pole. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z - 1 ≠ 0) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      z :=
  zetaCompletedExplicitFormulaCorrectionOnePole_differentiableAt_off_pole
    f hPhi hz

/-- The named isolated `s = 1` correction kernel is continuous away from its
pole. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z - 1 ≠ 0) :
    ContinuousAt
      (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      z :=
  (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_off_pole
    f hPhi hz).continuousAt

/-- The local coefficient of the isolated `s = 1` correction kernel is continuous
on every deleted disk around the pole. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_deletedCircleCoefficient_continuousOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) (R : ℝ) :
    ContinuousOn
      (fun z : ℂ =>
        (z - 1) *
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      (Metric.closedBall (1 : ℂ) R \ {(1 : ℂ)}) := by
  intro z hz
  have hz_ne : z - 1 ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 :=
      sub_eq_zero.mp hzero
    have hmem : z ∈ ({(1 : ℂ)} : Set ℂ) := by
      exact hz_eq
    exact hz.2 hmem
  have hleft :
      ContinuousAt (fun w : ℂ => w - 1) z :=
    (continuous_id.sub continuous_const).continuousAt
  have hright :
      ContinuousAt
        (fun w : ℂ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
        z :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousAt_off_pole
      f hPhi hz_ne
  exact (hleft.mul hright).continuousWithinAt

/-- Radius-parametric differentiability of the local coefficient of the isolated
`s = 1` correction kernel on a deleted disk. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_deletedCircleCoefficient_differentiableAt_of_mem
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) {R : ℝ} {z : ℂ}
    (hz : z ∈ ((Metric.ball (1 : ℂ) R \ {(1 : ℂ)}) \ (∅ : Set ℂ))) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        (w - 1) *
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      z := by
  have hz_not_mem : z ∉ ({(1 : ℂ)} : Set ℂ) :=
    hz.1.2
  have hz_ne : z - 1 ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 :=
      sub_eq_zero.mp hzero
    have hmem : z ∈ ({(1 : ℂ)} : Set ℂ) := by
      exact hz_eq
    exact hz_not_mem hmem
  have hleft :
      DifferentiableAt ℂ (fun w : ℂ => w - 1) z :=
    differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
  have hright :
      DifferentiableAt ℂ
        (fun w : ℂ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
        z :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_off_pole
      f hPhi hz_ne
  exact hleft.mul hright

/-- Deleted-circle residue theorem for the isolated `s = 1` correction kernel
with all deleted-disk regularity discharged in the single-pole owner layer. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_deletedCircleIntegral_eq_twoPiI_smul_residue_of_pos_radius
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    (∮ z in C((1 : ℂ), R),
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionOnePole_deletedCircleIntegral_eq_twoPiI_smul_residue
      f hPhi hR (∅ : Set ℂ) Set.countable_empty
      (zetaCompletedExplicitFormulaCorrectionOnePole_deletedCircleCoefficient_continuousOn
        f hPhi R)
      (fun z hz =>
        zetaCompletedExplicitFormulaCorrectionOnePole_deletedCircleCoefficient_differentiableAt_of_mem
          f hPhi hz)

/-- Boundary avoidance excludes the isolated `s = 1` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_ne_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    z - 1 ≠ 0 := by
  intro hz
  have hone : z = 1 :=
    sub_eq_zero.mp hz
  have hsingular : explicitFormulaContourSingularPoint z :=
    Or.inr (Or.inl hone)
  exact havoid z hsingular hboundary

/-- The isolated `s = 1` correction kernel is regular at every avoided boundary point. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_regularAt_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    ContinuousAt
        (fun w : ℂ =>
          (-1 / (w - 1)) *
            zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z ∧
      DifferentiableAt ℂ
        (fun w : ℂ =>
          (-1 / (w - 1)) *
            zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z := by
  have hz :
      z - 1 ≠ 0 :=
    zetaCompletedExplicitFormulaCorrectionOnePole_ne_of_avoidsBoundary
      F T havoid hboundary
  exact And.intro
    (zetaCompletedExplicitFormulaCorrectionOnePole_continuousAt_off_pole f hPhi hz)
    (zetaCompletedExplicitFormulaCorrectionOnePole_differentiableAt_off_pole f hPhi hz)

/-- The isolated `s = 1` correction kernel is regular at every boundary point of
an avoided rectangle. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_regularAt_all_boundary_points_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F T →
        ContinuousAt
            (fun w : ℂ =>
              (-1 / (w - 1)) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (-1 / (w - 1)) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z :=
  fun _ hz =>
    zetaCompletedExplicitFormulaCorrectionOnePole_regularAt_boundary_of_avoidsBoundary
      f F hPhi T havoid hz

/-- The named isolated `s = 1` correction kernel is regular at every boundary
point of an avoided rectangle. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_regularAt_all_boundary_points_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F T →
        ContinuousAt
            (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z := by
  intro z hboundary
  have hz :
      z - 1 ≠ 0 :=
    zetaCompletedExplicitFormulaCorrectionOnePole_ne_of_avoidsBoundary
      F T havoid hboundary
  exact And.intro
    (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousAt_off_pole
      f hPhi hz)
    (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_off_pole
      f hPhi hz)

/-- The isolated `s = 1` correction kernel is continuous on every avoided rectangle
boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_continuousOn_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ContinuousOn
      (fun w : ℂ =>
        (-1 / (w - 1)) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      (explicitFormulaContourFamilyBoundary F T) := by
  intro z hz
  exact
    (zetaCompletedExplicitFormulaCorrectionOnePole_regularAt_all_boundary_points_of_avoidsBoundary
      f F hPhi T havoid z hz).1.continuousWithinAt

/-- The named isolated `s = 1` correction kernel is continuous on every avoided
rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ContinuousOn
      (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      (explicitFormulaContourFamilyBoundary F T) := by
  intro z hz
  exact
    (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_regularAt_all_boundary_points_of_avoidsBoundary
      f F hPhi T havoid z hz).1.continuousWithinAt

/-- Positive-height residue inputs for the isolated `s = 1` correction kernel:
the pole is inside the rectangle, the kernel is regular on the avoided boundary,
and the local residue is the already computed one-pole residue. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_tangentResidueInputs_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (hT : 0 < T)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (1 : ℂ) ∈ explicitFormulaContourFamilyInterior F T ∧
      (∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
              z ∧
            DifferentiableAt ℂ
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
              z) ∧
      Tendsto
        (fun z : ℂ =>
          (z - 1) *
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (𝓝[≠] (1 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 / 2))) := by
  have hinterior :
      (1 : ℂ) ∈ explicitFormulaContourFamilyInterior F T :=
    explicitFormulaContourFamilyInterior_one_mem F T hT
  have hregular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
              z ∧
            DifferentiableAt ℂ
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
              z :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_regularAt_all_boundary_points_of_avoidsBoundary
      f F hPhi T havoid
  have hlocal :
      Tendsto
        (fun z : ℂ =>
          (z - 1) *
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (𝓝[≠] (1 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_localResidue_tendsto
      f hPhi
  exact And.intro hinterior (And.intro hregular hlocal)

/-- A one-pole kernel restricted to a continuous real parametrized segment is
interval-integrable once the complex kernel is continuous on that segment
image. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_param_intervalIntegrable_of_continuousOn
    (f : ZetaAdmissibleFunction)
    (γ : ℝ → ℂ)
    {a b : ℝ}
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (hkernel :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (γ '' Set.uIcc a b)) :
    IntervalIntegrable
      (fun x : ℝ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f (γ x))
      volume a b := by
  have hmaps :
      Set.MapsTo γ (Set.uIcc a b) (γ '' Set.uIcc a b) := by
    intro x hx
    exact Set.mem_image_of_mem γ hx
  have hcont :
      ContinuousOn
        (fun x : ℝ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f (γ x))
      (Set.uIcc a b) :=
    ContinuousOn.comp hkernel hγ hmaps
  exact hcont.intervalIntegrable

/-- The isolated one-pole correction kernel is continuous on any set that avoids
the pole `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_of_avoids_pole
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (s : Set ℂ)
    (havoid : ∀ z : ℂ, z ∈ s → z - 1 ≠ 0) :
    ContinuousOn
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      s := by
  intro z hz
  exact
    (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousAt_off_pole
      f hPhi (havoid z hz)).continuousWithinAt

/-- Combined off-pole parametrized segment integrability for the one-pole
correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_param_intervalIntegrable_of_avoids_pole
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (γ : ℝ → ℂ)
    {a b : ℝ}
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (havoid : ∀ z : ℂ, z ∈ γ '' Set.uIcc a b → z - 1 ≠ 0) :
    IntervalIntegrable
      (fun x : ℝ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f (γ x))
      volume a b := by
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_param_intervalIntegrable_of_continuousOn
      f γ hγ
      (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_of_avoids_pole
        f hPhi (γ '' Set.uIcc a b) havoid)

/-- Horizontal affine line parametrizations used by one-pole rectangular
subsegments are continuous on every real interval. -/
theorem zetaExplicitFormulaOnePole_horizontalAffine_continuousOn
    (y : ℝ) (a b : ℝ) :
    ContinuousOn
      (fun x : ℝ => (x : ℂ) + y * Complex.I)
      (Set.uIcc a b) :=
  (Complex.continuous_ofReal.add continuous_const).continuousOn

/-- Vertical affine line parametrizations used by one-pole rectangular
subsegments are continuous on every real interval. -/
theorem zetaExplicitFormulaOnePole_verticalAffine_continuousOn
    (x : ℝ) (a b : ℝ) :
    ContinuousOn
      (fun y : ℝ => (x : ℂ) + y * Complex.I)
      (Set.uIcc a b) :=
  (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn

/-- Horizontal rectangular one-pole segment integrability from off-pole image
avoidance. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_horizontal_intervalIntegrable_of_avoids_pole
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (y : ℝ)
    (a b : ℝ)
    (havoid :
      ∀ z : ℂ,
        z ∈ (fun x : ℝ => (x : ℂ) + y * Complex.I) '' Set.uIcc a b →
          z - 1 ≠ 0) :
    IntervalIntegrable
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          ((x : ℂ) + y * Complex.I))
      volume a b := by
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_param_intervalIntegrable_of_avoids_pole
      f hPhi (fun x : ℝ => (x : ℂ) + y * Complex.I)
      (zetaExplicitFormulaOnePole_horizontalAffine_continuousOn y a b)
      havoid

/-- Vertical rectangular one-pole segment integrability from off-pole image
avoidance. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_vertical_intervalIntegrable_of_avoids_pole
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (x : ℝ)
    (a b : ℝ)
    (havoid :
      ∀ z : ℂ,
        z ∈ (fun y : ℝ => (x : ℂ) + y * Complex.I) '' Set.uIcc a b →
          z - 1 ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          ((x : ℂ) + y * Complex.I))
      volume a b := by
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_param_intervalIntegrable_of_avoids_pole
      f hPhi (fun y : ℝ => (x : ℂ) + y * Complex.I)
      (zetaExplicitFormulaOnePole_verticalAffine_continuousOn x a b)
      havoid

/-- Canonical one-pole square-punctured boundary bookkeeping: the punctured
outer rectangle boundary is the four-cell boundary sum around the isolated
`s = 1` square.

This is pure finite contour accounting.  It owns no Cauchy theorem and no
residue computation; it only identifies the two boundary expressions at the
canonical puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_canonicalSquarePuncturedBoundary_eq_fourCellBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) := by
  sorry

/-- Canonical one-pole four-cell Cauchy cancellation for the isolated `s = 1`
correction kernel.

The geometric square bookkeeping and local residue calculation are deliberately
not part of this theorem; this is only the Cauchy-Goursat vanishing of the four
regular cells. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_canonicalFourCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 := by
  sorry

/-- Canonical one-pole inner-square residue value for the isolated `s = 1`
correction kernel.

This is the square-contour residue input corresponding to the local residue
`-Phi f (1 / 2)`. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_canonicalInnerSquareBoundary_eq_residue_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  sorry

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
