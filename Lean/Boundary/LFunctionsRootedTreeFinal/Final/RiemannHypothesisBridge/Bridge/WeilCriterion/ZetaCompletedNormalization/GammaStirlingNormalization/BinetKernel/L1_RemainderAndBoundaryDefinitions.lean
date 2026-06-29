import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.A_RealAnalysisBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.I_LocalIndentationAbsorption
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.J_ContourKernelAccounting
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.H_TailRemainderEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.K_BranchCoherence
import Mathlib

import Mathlib

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetTailContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary

namespace Boundary
namespace LFunctions

noncomputable section

namespace LFunctions

noncomputable section

theorem Complex.binetSecondFormula_small_remainder_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaSmallRemainder w‖ ≤
      4 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  exact Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
    (w := w) hw_re_pos

/-- Honest split-bound mirror for the Binet remainder on the open right half-plane.

This is the shape owned classically by
`Complex.binetSecondFormulaRemainder_norm_le_openRightHalfPlane`: the lower
part of the Binet kernel gives the `1 / ‖w‖` term, while the tail remains a
fixed-`w` majorant.  It is intentionally not a pure `O(1 / ‖w‖)` statement. -/
theorem Complex.binetSecondFormula_remainder_split_bound_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖Complex.binetSecondFormulaRemainder w‖ ≤
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
          2 * C *
            (∫ t : ℝ in Set.Ioi (0 : ℝ),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let S : ℂ := Complex.binetSecondFormulaSmallRemainder w
  let T : ℂ := Complex.binetSecondFormulaTailRemainder w
  have hsplit : Complex.binetSecondFormulaRemainder w = S + T := by
    exact Complex.binetSecondFormulaRemainder_eq_small_add_tail (w := w) hw_re_pos
  have hS : ‖S‖ ≤ 4 * J / ‖w‖ := by
    exact Complex.binetSecondFormula_small_remainder_norm_le_integral_majorant
      (w := w) hw_re_pos
  match Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
      (w := w) hw_re_pos with
  | ⟨C, hC_nonneg, hT⟩ =>
      let hT_named : ‖T‖ ≤ 2 * C * J := hT
      let hsum : ‖S + T‖ ≤ 4 * J / ‖w‖ + 2 * C * J :=
        calc
          ‖S + T‖ ≤ ‖S‖ + ‖T‖ :=
            norm_add_le S T
          _ ≤ 4 * J / ‖w‖ + 2 * C * J :=
            add_le_add hS hT_named
      exact
        ⟨C, hC_nonneg,
          Eq.subst
            (motive := fun z : ℂ =>
              ‖z‖ ≤
                4 * J / ‖w‖ + 2 * C * J)
            hsplit.symm
            hsum⟩

/-- Binet's second formula with the honest split remainder bound on the open
right half-plane. -/
theorem Complex.binetSecondFormula_logGamma_with_split_remainder_bound_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          Complex.binetLogGammaBranch w =
              Complex.binetLogGammaMainTerm w +
                Complex.binetSecondFormulaRemainder w ∧
            ∃ C : ℝ,
              0 ≤ C ∧
              ‖Complex.binetSecondFormulaRemainder w‖ ≤
                4 *
                  (∫ t : ℝ in Set.Ioi (0 : ℝ),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
                  2 * C *
                    (∫ t : ℝ in Set.Ioi (0 : ℝ),
                      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius with
  | ⟨Rlog, hRlog, hlog⟩ =>
      exact
        ⟨Rlog, 1, hRlog, zero_lt_one,
          fun w hw_re_pos hw_norm =>
            ⟨hlog w hw_re_pos hw_norm,
              Complex.binetSecondFormula_remainder_split_bound_openRightHalfPlane hw_re_pos⟩⟩

/-- Existence of a branch-safe contour-deformed Binet tail kernel with
uniform full-sector majorization. -/
def Complex.BinetSecondFormulaBranchUniformTailAbsorption : Prop :=
  (∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) ∧
  Complex.BinetSecondFormulaBranchCoherence

/-- The branch-wall local-indentation envelope appearing in the full-sector
Binet contour estimate. -/
noncomputable def Complex.binetSecondFormulaBranchLocalIndentationEnvelope
    (w : ℂ) : ℝ :=
  2 *
    (((max |Real.log (w.re / (3 * ‖w‖))|
        (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
      (Real.exp (Real.pi * ‖w‖) - 1)) *
      (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal)

/-- Honest full-sector Binet tail estimate before local-indentation
absorption.

This is the estimate supplied by the contour calculation in the open right
half-plane.  It keeps the branch-wall logarithmic envelope explicit; the pure
`C / ‖w‖` tail package is a strictly stronger absorption theorem. -/
def Complex.BinetSecondFormulaBranchLocalIndentationTailControl : Prop :=
  ∃ Cfar : ℝ,
    0 ≤ Cfar ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
          Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
            (Cfar / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w

/-- Honest tail-remainder estimate before local-indentation absorption.

This is the tail-remainder version of
`BinetSecondFormulaBranchLocalIndentationTailControl`: it transfers the
principal-tail integral estimate to the actual Binet tail remainder while
keeping the branch-wall local-indentation envelope explicit. -/
def Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl : Prop :=
  ∃ Cfar : ℝ,
    0 ≤ Cfar ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
          Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
            (Cfar / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local absorption of the Binet branch-wall local-indentation
envelope.

The pointwise logarithmic envelope is uniformly absorbable only after staying
a fixed angular distance away from the branch wall, and only at the natural
scale of the Binet decaying-tail integral.  The stronger pure
`C / ‖w‖` scale is not a consequence of this scalar window estimate: the
bounded indentation window has length comparable to `‖w‖`.  The full-sector
pure tail theorem must therefore use paired contour cancellation rather than
this local scalar absorption. -/
def Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            Complex.binetSecondFormulaBranchLocalIndentationEnvelope w ≤
              C * Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local pre-cancellation tail-remainder absorption.

Away from the branch wall, the local-indentation envelope can be absorbed
into the standard decaying tail, leaving a sector-local tail-remainder bound.
This is weaker than full branch-wall contour cancellation because the constant
depends on the angular margin `δ`. -/
def Complex.BinetSecondFormulaTailRemainderSectorLocalAbsorption : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
              (C + C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w

/-- Legacy full-sector principal-tail norm estimate.

This raw norm statement is stronger than the canonical contour-level target
used by the owner package below.  It is retained only as a compatibility
predicate for older bookkeeping lemmas; the owner theorem for branch-wall
cancellation is `BinetSecondFormulaBranchWallContourCancellationTailAbsorption`. -/
def Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation : Prop :=
  ∃ C : ℝ,
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local real-variable comparison for the logarithmic
local-indentation envelope.

This is the scalar estimate behind local-indentation absorption: after fixing
an angular margin `δ`, the branch-wall logarithmic window is bounded by the
standard Binet decaying-tail integral at the scale-correct constant loss. -/
def Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            Complex.binetSecondFormulaBranchLocalIndentationEnvelope w ≤
              C * Complex.binetSecondFormulaDecayingTailIntegral w

/-- Legacy paired-contour name for the principal-tail norm estimate.

This has the same raw-norm content as
`BinetSecondFormulaBranchWallPrincipalTailCancellation`.  The non-circular
owner target is the contour-cancellation tail-absorption predicate below. -/
def Complex.BinetSecondFormulaBranchWallPairedContourPrincipalTailCancellation : Prop :=
  ∃ C : ℝ,
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Full-sector Binet tail absorption after branch-wall contour cancellation.

This is the canonical replacement for pointwise branch-wall envelope
absorption: away from the wall one uses sector-local absorption, while near
the wall the paired indentation contributions must cancel at the contour
level before taking the final tail norm. -/
def Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption : Prop :=
  ∃ R : ℝ, ∃ C : ℝ,
    0 < R ∧
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Owner target for the branch-wall lower-vertical cancellation estimate.

This is the cancellation-before-norm statement in Abel-Plana vertical-side
coordinates.  It is equivalent to the public tail-absorption theorem by the
proved lower-vertical split, but it keeps the analytic leaf attached to the
place where the wall terms actually cancel: the full lower vertical side with
the fixed initial Binet window removed. -/
def Complex.BinetSecondFormulaLowerVerticalDifferenceDecay : Prop :=
  ∃ R : ℝ, ∃ C : ℝ,
    0 < R ∧
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Finite-height lower-vertical cancellation estimate.

This is the finite-height analytic form of branch-wall cancellation before
passing to the improper lower vertical limit.  It is equivalent to the
endpoint-returned restored pair formulation by the proved endpoint-returned
norm identity. -/
def Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay : Prop :=
  ∃ R : ℝ, ∃ C : ℝ,
    0 < R ∧
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∀ᶠ T : ℝ in atTop,
          ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
              Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
            (C / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w

/-- Endpoint-returned restored paired finite-height decay target.

This is the canonical endpoint-restored analytic leaf for branch-wall
cancellation.  The restored static expression and restored contour error are
paired before taking norms, with the half-endpoint term returned to both
members of the pair.  This avoids the false separate-estimate route where the
restored static limit carries a half-endpoint defect while the restored contour
error tends to zero. -/
def Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay : Prop :=
  ∃ R : ℝ, ∃ C : ℝ,
    0 < R ∧
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∃ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ‖(((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
              Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
              Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
              Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
              (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
                Complex.finiteAbelPlanaLogSummandHalfEndpoints N w))‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w

/-- Quantitative solved-static Abel-Plana boundary decay.

This is the norm estimate for the solved static boundary expression alone,
with the boundary-target identity deliberately not bundled into the predicate.
The boundary target is structural Abel-Plana assembly; this predicate is the
remaining scale estimate for the static expression after subtracting the
initial lower-vertical Binet window. -/
def Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate : Prop :=
  ∃ R : ℝ, ∃ Cstatic : ℝ,
    0 < R ∧
    2 ≤ R ∧
    0 < Cstatic ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∃ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
              Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
              Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
              Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (Cstatic / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w

/-- Historical endpoint-free structural finite-height boundary target used by
the older solved-static Abel-Plana wall-cancellation estimate.

The endpoint-restored target below is the canonical target produced by the
real-segment constant-face reconstruction.  The endpoint-free target is
compatible with that reconstruction only if the endpoint indentation vanishes;
see
`binetSecondFormula_boundaryTarget_and_realSegmentConstantFaces_imply_endpointIndentation_eventually_zero`. -/
def Complex.BinetSecondFormulaFiniteHeightBoundaryTarget : Prop :=
  ∃ R : ℝ,
    0 < R ∧
    2 ≤ R ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
              ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
              Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T

/-- Structural finite-height boundary target with endpoint indentation kept
explicit.

This is the endpoint-restored target naturally produced when the two scaled
cotangent constant faces reconstruct only the real segment. -/
def Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored : Prop :=
  ∃ R : ℝ,
    0 < R ∧
    2 ≤ R ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
              ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
              Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) =
              Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T

/-- Structural constant-face reconstruction target for the finite-height
Abel-Plana rectangle.

This is the actual algebraic content supplied by the two scaled cotangent
constant faces: together they reconstruct the real segment, while endpoint
indentation is supplied separately by the principal-value endpoint owner. -/
def Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces : Prop :=
  ∃ R : ℝ,
    0 < R ∧
    2 ≤ R ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) =
              (let M : ℕ := N + 1;
                ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                  Complex.finiteAbelPlanaLogSummand w (x : ℂ))

/-- Owner wrapper from a pointwise constant-face reconstruction to the
large-radius real-segment constant-face predicate. -/
theorem Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_of_pointwise
    (hpoint :
      ∀ w : ℂ,
        0 < w.re →
          ∀ N : ℕ,
            ∀ T : ℝ,
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
                ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) =
                (let M : ℕ := N + 1;
                  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ))) :
    Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces := by
  exact
    ⟨2, zero_lt_two, le_refl (2 : ℝ),
      fun w hw_re_pos _hRle N =>
        eventually_of_forall
          (fun T => hpoint w hw_re_pos N T)⟩

/-- Endpoint-restored boundary target from real-segment constant-face
reconstruction. -/
theorem Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored := by
  match hconstant with
  | ⟨R, hR_pos, hR_two, hconstant_bound⟩ =>
      exact
        ⟨R, hR_pos, hR_two,
          fun w hw_re_pos hRle N =>
            (hconstant_bound w hw_re_pos hRle N).mono
              (fun T hconstantT =>
                Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_endpointRestored_of_realSegmentConstantFaces
                  N w T hconstantT)⟩

/-- Endpoint-restored structural boundary target from the pointwise
constant-face reconstruction. -/
theorem Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_pointwise_realSegmentConstantFaces
    (hpoint :
      ∀ w : ℂ,
        0 < w.re →
          ∀ N : ℕ,
            ∀ T : ℝ,
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
                ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) =
                (let M : ℕ := N + 1;
                  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ))) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored := by
  have hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces :=
    Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_of_pointwise
      hpoint
  exact
    Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
      hconstant

/-- Owner theorem for the real-segment constant-face reconstruction. -/
theorem Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner :
    Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces := by
  exact
    Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_of_pointwise
      (fun w hw_re_pos N T =>
        Complex.finiteAbelPlana_log_realSegmentConstantFaces N hw_re_pos T)

/-- Owner theorem for the endpoint-restored finite-height structural boundary
target. -/
theorem Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_owner :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored := by
  exact
    Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
      Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner

/-- If an expression and the same expression with an added endpoint term both
equal the same target, then the endpoint term is zero. -/
theorem Complex.endpoint_zero_of_boundary_target_and_endpoint_restored
    {X E Y : ℂ}
    (hplain : X = Y)
    (hrestored : X + E = Y) :
    E = 0 := by
  have hXE_eq_X : X + E = X := by
    exact Eq.trans hrestored hplain.symm
  calc
    E = (X + E) - X := by
      exact (add_sub_cancel_left X E).symm
    _ = X - X := by
      exact congrArg (fun z : ℂ => z - X) hXE_eq_X
    _ = 0 := sub_self X

/-- Pointwise incompatibility of the endpoint-free and endpoint-restored
finite-height targets unless the endpoint indentation itself vanishes. -/
theorem Complex.finiteHeightBoundaryTarget_and_endpointRestored_imply_endpointIndentation_zero
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hplain :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)
    (hrestored :
      ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) =
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w = 0 := by
  exact
    Complex.endpoint_zero_of_boundary_target_and_endpoint_restored
      hplain hrestored

/-- At the first finite Abel-Plana window and `w = 1`, the endpoint
principal-value indentation is nonzero.

This pins down the obstruction to the historical endpoint-free target: the
endpoint term is the half-endpoint contribution, not a height-dependent contour
error that can disappear at large finite height. -/
theorem Complex.finiteAbelPlanaLogEndpointPVIndentationContribution_at_zero_one_ne_zero :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (1 : ℂ) ≠ 0 := by
  have hlog_one : Complex.log (1 : ℂ) = 0 :=
    Complex.log_one
  have hlog_two_re :
      (Complex.log (2 : ℂ)).re = Real.log 2 :=
    Complex.log_ofReal_re 2
  have hreal_log_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hcomplex_log_two_ne_zero : Complex.log (2 : ℂ) ≠ 0 := by
    intro hzero
    have hre_zero : (Complex.log (2 : ℂ)).re = 0 :=
      congrArg Complex.re hzero
    have hreal_zero : Real.log 2 = 0 :=
      Eq.trans hlog_two_re.symm hre_zero
    exact (ne_of_gt hreal_log_two_pos) hreal_zero
  have htwo_ne_zero : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  have hlog_two_div_two_ne_zero : Complex.log (2 : ℂ) / (2 : ℂ) ≠ 0 := by
    intro hdiv_zero
    have hmul_zero :
        (Complex.log (2 : ℂ) / (2 : ℂ)) * (2 : ℂ) = 0 * (2 : ℂ) :=
      congrArg (fun z : ℂ => z * (2 : ℂ)) hdiv_zero
    have hlog_two_zero : Complex.log (2 : ℂ) = 0 := by
      calc
        Complex.log (2 : ℂ) =
            (Complex.log (2 : ℂ) / (2 : ℂ)) * (2 : ℂ) := by
          exact (div_mul_cancel₀ (Complex.log (2 : ℂ)) htwo_ne_zero).symm
        _ = 0 * (2 : ℂ) := hmul_zero
        _ = 0 := zero_mul (2 : ℂ)
    exact hcomplex_log_two_ne_zero hlog_two_zero
  have hendpoint_eq :
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (1 : ℂ) =
        Complex.log (2 : ℂ) / (2 : ℂ) := by
    calc
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (1 : ℂ) =
          Complex.finiteAbelPlanaLogSummandHalfEndpoints 0 (1 : ℂ) := by
        exact
          Complex.finiteAbelPlana_log_endpointPVIndentationContribution_eq_halfEndpoints
            0 (1 : ℂ)
      _ = (Complex.log (1 : ℂ) + Complex.log ((1 : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        rfl
      _ = (0 + Complex.log ((1 : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        exact congrArg (fun z : ℂ => (z + Complex.log ((1 : ℂ) + (1 : ℂ))) / (2 : ℂ)) hlog_one
      _ = Complex.log ((1 : ℂ) + (1 : ℂ)) / (2 : ℂ) := by
        exact congrArg (fun z : ℂ => z / (2 : ℂ)) (zero_add (Complex.log ((1 : ℂ) + (1 : ℂ))))
      _ = Complex.log (2 : ℂ) / (2 : ℂ) := by
        have hone_add_one : (1 : ℂ) + (1 : ℂ) = 2 := by
          rfl
        exact congrArg (fun z : ℂ => Complex.log z / (2 : ℂ)) hone_add_one
  intro hendpoint_zero
  exact hlog_two_div_two_ne_zero (Eq.trans hendpoint_eq.symm hendpoint_zero)

/-- On the real half-line `x ≥ 1`, the first endpoint principal-value
indentation is nonzero.

This is the large-radius version of the endpoint obstruction: the
endpoint-free target cannot be recovered from the real-segment constant-face
reconstruction by passing to sufficiently large heights or radii. -/
theorem Complex.finiteAbelPlanaLogEndpointPVIndentationContribution_at_zero_ofReal_ge_one_ne_zero
    {x : ℝ}
    (hx : 1 ≤ x) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) ≠ 0 := by
  have hx_nonneg : 0 ≤ x :=
    le_trans zero_le_one hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_one hx
  have hx_one_pos : 0 < x + 1 :=
    add_pos hx_pos zero_lt_one
  have hx_one_nonneg : 0 ≤ x + 1 :=
    le_of_lt hx_one_pos
  have hx_one_gt_one : 1 < x + 1 :=
    lt_add_of_pos_right x zero_lt_one
  have hlog_x_nonneg : 0 ≤ Real.log x :=
    Real.log_nonneg hx
  have hlog_x_one_pos : 0 < Real.log (x + 1) :=
    Real.log_pos hx_one_gt_one
  have hsum_pos : 0 < Real.log x + Real.log (x + 1) :=
    add_pos_of_nonneg_of_pos hlog_x_nonneg hlog_x_one_pos
  have hhalf_pos : 0 < (Real.log x + Real.log (x + 1)) / 2 :=
    div_pos hsum_pos zero_lt_two
  have hhalf_ne_zero : (Real.log x + Real.log (x + 1)) / 2 ≠ 0 :=
    ne_of_gt hhalf_pos
  have hlog_x :
      Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hx_nonneg).symm
  have hx_one_cast :
      (x : ℂ) + (1 : ℂ) = ((x + 1 : ℝ) : ℂ) :=
    (Complex.ofReal_add x 1).symm
  have hlog_x_one :
      Complex.log ((x : ℂ) + (1 : ℂ)) = (Real.log (x + 1) : ℂ) := by
    exact Eq.trans
      (congrArg Complex.log hx_one_cast)
      (Complex.ofReal_log hx_one_nonneg).symm
  have hendpoint_eq :
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) =
        (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) := by
    calc
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) =
          Complex.finiteAbelPlanaLogSummandHalfEndpoints 0 (x : ℂ) := by
        exact
          Complex.finiteAbelPlana_log_endpointPVIndentationContribution_eq_halfEndpoints
            0 (x : ℂ)
      _ = (Complex.log (x : ℂ) + Complex.log ((x : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        rfl
      _ = ((Real.log x : ℂ) + Complex.log ((x : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        exact congrArg
          (fun z : ℂ => (z + Complex.log ((x : ℂ) + (1 : ℂ))) / (2 : ℂ))
          hlog_x
      _ = ((Real.log x : ℂ) + (Real.log (x + 1) : ℂ)) / (2 : ℂ) := by
        exact congrArg
          (fun z : ℂ => ((Real.log x : ℂ) + z) / (2 : ℂ))
          hlog_x_one
      _ = ((Real.log x + Real.log (x + 1) : ℝ) : ℂ) / (2 : ℂ) := by
        exact congrArg
          (fun z : ℂ => z / (2 : ℂ))
          (Complex.ofReal_add (Real.log x) (Real.log (x + 1))).symm
      _ = (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) := by
        exact (Complex.ofReal_div (Real.log x + Real.log (x + 1)) 2).symm
  intro hendpoint_zero
  have hhalf_cast_zero :
      (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) = 0 :=
    Eq.trans hendpoint_eq.symm hendpoint_zero
  have hhalf_cast_ne_zero :
      (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) ≠ 0 :=
    (Complex.ofReal_ne_zero).mpr hhalf_ne_zero
  exact hhalf_cast_ne_zero hhalf_cast_zero

/-- Predicate-level obstruction: the endpoint-free boundary target is
compatible with the real-segment constant-face reconstruction only if the
endpoint indentation contribution eventually vanishes. -/
theorem Complex.binetSecondFormula_boundaryTarget_and_realSegmentConstantFaces_imply_endpointIndentation_eventually_zero
    (hplain :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    ∃ R : ℝ,
      0 < R ∧
      2 ≤ R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ N : ℕ,
            ∀ᶠ T : ℝ in atTop,
              Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w = 0 := by
  match hplain with
  | ⟨Rplain, hRplain_pos, hRplain_two, hplain_bound⟩ =>
      match
        Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
          hconstant
      with
      | ⟨Rrestored, _hRrestored_pos, _hRrestored_two, hrestored_bound⟩ =>
          let R : ℝ := max Rplain Rrestored
          have hR_pos : 0 < R :=
            lt_of_lt_of_le hRplain_pos (le_max_left Rplain Rrestored)
          have hR_two : 2 ≤ R :=
            le_trans hRplain_two (le_max_left Rplain Rrestored)
          exact
            ⟨R, hR_pos, hR_two,
              fun w hw_re_pos hRle N =>
                have hRplain_le : Rplain ≤ ‖w‖ :=
                  le_trans (le_max_left Rplain Rrestored) hRle
                have hRrestored_le : Rrestored ≤ ‖w‖ :=
                  le_trans (le_max_right Rplain Rrestored) hRle
                have hplain_T :
                    ∀ᶠ T : ℝ in atTop,
                      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                              Complex.I *
                                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                  hplain_bound w hw_re_pos hRplain_le N
                have hrestored_T :
                    ∀ᶠ T : ℝ in atTop,
                      ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                              Complex.I *
                                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
                        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) =
                        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                  hrestored_bound w hw_re_pos hRrestored_le N
                (hplain_T.and hrestored_T).mono
                  (fun T hpair =>
                    Complex.finiteHeightBoundaryTarget_and_endpointRestored_imply_endpointIndentation_zero
                      N w T hpair.1 hpair.2)⟩

/-- The historical endpoint-free finite-height target is incompatible with
the canonical real-segment reconstruction of the two constant cotangent faces.

The contradiction is obtained on the real half-line at `N = 0`: the two
structural targets force the endpoint indentation to be eventually zero, while
the endpoint owner calculation shows it is nonzero for every real `w ≥ 1`. -/
theorem Complex.not_boundaryTarget_and_realSegmentConstantFaces
    (hplain :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    False := by
  match
    Complex.binetSecondFormula_boundaryTarget_and_realSegmentConstantFaces_imply_endpointIndentation_eventually_zero
      hplain hconstant
  with
  | ⟨R, _hR_pos, _hR_two, hzero_bound⟩ =>
      let x : ℝ := max R 1
      have hx_ge_one : 1 ≤ x :=
        le_max_right R 1
      have hx_pos : 0 < x :=
        lt_of_lt_of_le zero_lt_one hx_ge_one
      have hx_complex_re_pos : 0 < ((x : ℂ).re) :=
        hx_pos
      have hx_nonneg : 0 ≤ x :=
        le_of_lt hx_pos
      have hRle_x : R ≤ x :=
        le_max_left R 1
      have hnorm_eq : ‖(x : ℂ)‖ = x :=
        Eq.trans (Complex.norm_real x) (Real.norm_of_nonneg hx_nonneg)
      have hRle_norm : R ≤ ‖(x : ℂ)‖ :=
        Eq.subst
          (motive := fun y : ℝ => R ≤ y)
          hnorm_eq.symm
          hRle_x
      have hzero_eventual :
          ∀ᶠ T : ℝ in atTop,
            Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) = 0 :=
        hzero_bound (x : ℂ) hx_complex_re_pos hRle_norm 0
      have hzero :
          Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) = 0 :=
        (eventually_const.mp hzero_eventual)
      exact
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution_at_zero_ofReal_ge_one_ne_zero
          hx_ge_one hzero

/-- Owner obstruction to the historical endpoint-free finite-height boundary
target.

The owner-level constant-face reconstruction has now been proved, and it is
the canonical reconstruction of the real segment.  Combined with the endpoint
calculation, it rules out the historical endpoint-free target outright. -/
theorem Complex.not_binetSecondFormula_finiteHeightBoundaryTarget_owner :
    ¬ Complex.BinetSecondFormulaFiniteHeightBoundaryTarget := by
  intro hplain
  exact
    Complex.not_boundaryTarget_and_realSegmentConstantFaces
      hplain
      Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner

/-- The historical solved-static input pair is not the correct owner target.

Its first component is the endpoint-free finite-height boundary target, which
is incompatible with the canonical real-segment constant-face reconstruction. -/
theorem Complex.not_binetSecondFormula_boundarySolvedStatic_inputs_owner_target :
    ¬ (Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
        Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate) := by
  intro hinputs
  exact
    Complex.not_binetSecondFormula_finiteHeightBoundaryTarget_owner
      hinputs.1

/-- Corrected endpoint-restored finite-height contour input package.

This is the structural input actually produced by the canonical constant-face
algebra: the boundary target keeps the endpoint indentation, and the contour
error is the endpoint-restored contour error with that indentation subtracted. -/
def Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs : Prop :=
  Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored ∧

end
end LFunctions
end Boundary
