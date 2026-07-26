import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.ZetaPhiAnalyticControlCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.PhiRapidDecay.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaContourPaths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaTransformCalculusWeighted.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.ZetaAdmissibleDecay.Owner
import Mathlib.Analysis.Complex.Basic

/-!
# Boundary admissible transform regularity

This file owns the analytic control package for the explicit-formula transform
`Φ_f`. The point is to make the regularity hypotheses explicit at the owner
level so the contour theorem can consume them without ad hoc side conditions.

The file only records the package structure and the bridge lemmas that unpack
it. The actual analytic construction of the package belongs upstream in the
transform theory.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- `Φ_f` is differentiable along the right contour edge whenever the control package is present. -/
theorem ZetaPhiAnalyticControl.differentiableAt_rightPath
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath r t) :=
  h.differentiableAt_phi (zetaCompletedExplicitFormulaRightPath r t)

/-- The stored vertical-strip constant bounds `Phi_f` on the right contour edge. -/
theorem ZetaPhiAnalyticControl.rightPath_verticalStripConstantBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (t : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaRightPath r t).re)
    (hb : (zetaCompletedExplicitFormulaRightPath r t).re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightPath r t)‖
      ≤ h.verticalStripRapidDecayConstant a b N *
        (1 + ‖(zetaCompletedExplicitFormulaRightPath r t).im‖) ^ (-(N : ℤ)) :=
  h.verticalStripRapidDecayConstant_bound
    a b N (zetaCompletedExplicitFormulaRightPath r t) ha hb

/-- The vertical-strip bound of `Φ_f` applies to the right contour edge once the rectangle is
inside the chosen strip. -/
theorem ZetaPhiAnalyticControl.rightPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (t : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaRightPath r t).re)
    (hb : (zetaCompletedExplicitFormulaRightPath r t).re ≤ b) :
    ∃ C : ℝ,
      0 < C ∧
      ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightPath r t)‖
        ≤ C * (1 + ‖(zetaCompletedExplicitFormulaRightPath r t).im‖) ^ (-(N : ℤ)) := by
  exact
    ⟨h.verticalStripRapidDecayConstant a b N,
      h.verticalStripRapidDecayConstant_pos a b N,
      h.rightPath_verticalStripConstantBound a b N r t ha hb⟩

/-- The stored vertical-strip constant bounds `Phi_f` on the top contour edge. -/
theorem ZetaPhiAnalyticControl.topPath_verticalStripConstantBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaTopPath r x).re)
    (hb : (zetaCompletedExplicitFormulaTopPath r x).re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaTopPath r x)‖
      ≤ h.verticalStripRapidDecayConstant a b N *
        (1 + ‖(zetaCompletedExplicitFormulaTopPath r x).im‖) ^ (-(N : ℤ)) :=
  h.verticalStripRapidDecayConstant_bound
    a b N (zetaCompletedExplicitFormulaTopPath r x) ha hb

/-- The vertical-strip bound of `Φ_f` applies to the top contour edge once the rectangle is inside
the chosen strip. -/
theorem ZetaPhiAnalyticControl.topPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaTopPath r x).re)
    (hb : (zetaCompletedExplicitFormulaTopPath r x).re ≤ b) :
    ∃ C : ℝ,
      0 < C ∧
      ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaTopPath r x)‖
        ≤ C * (1 + ‖(zetaCompletedExplicitFormulaTopPath r x).im‖) ^ (-(N : ℤ)) := by
  exact
    ⟨h.verticalStripRapidDecayConstant a b N,
      h.verticalStripRapidDecayConstant_pos a b N,
      h.topPath_verticalStripConstantBound a b N r x ha hb⟩

/-- The stored vertical-strip constant bounds `Phi_f` on the bottom contour edge. -/
theorem ZetaPhiAnalyticControl.bottomPath_verticalStripConstantBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaBottomPath r x).re)
    (hb : (zetaCompletedExplicitFormulaBottomPath r x).re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaBottomPath r x)‖
      ≤ h.verticalStripRapidDecayConstant a b N *
        (1 + ‖(zetaCompletedExplicitFormulaBottomPath r x).im‖) ^ (-(N : ℤ)) :=
  h.verticalStripRapidDecayConstant_bound
    a b N (zetaCompletedExplicitFormulaBottomPath r x) ha hb

/-- The vertical-strip bound of `Φ_f` applies to the bottom contour edge once the rectangle is
inside the chosen strip. -/
theorem ZetaPhiAnalyticControl.bottomPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaBottomPath r x).re)
    (hb : (zetaCompletedExplicitFormulaBottomPath r x).re ≤ b) :
    ∃ C : ℝ,
      0 < C ∧
      ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaBottomPath r x)‖
        ≤ C * (1 + ‖(zetaCompletedExplicitFormulaBottomPath r x).im‖) ^ (-(N : ℤ)) := by
  exact
    ⟨h.verticalStripRapidDecayConstant a b N,
      h.verticalStripRapidDecayConstant_pos a b N,
      h.bottomPath_verticalStripConstantBound a b N r x ha hb⟩

/-- Compact support of the admissible source gives entireity of the completed Laplace
transform. -/
theorem zetaLaplaceTransform_entire_of_compactSupport
    (f : ZetaAdmissibleFunction) :
    AnalyticOn ℂ
      (fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z)
      Set.univ := by
  classical
  intro z _hz
  exact
    (Iff.mpr
        Complex.analyticAt_iff_eventually_differentiableAt
        (Filter.Eventually.of_forall
          (fun w : ℂ => Boundary.zetaLaplaceTransform_differentiableAt f w))).analyticWithinAt

/-- Compact support of the admissible source gives entireity of the completed explicit-formula
transform. -/
theorem zetaPhi_entire_of_compactSupport
    (f : ZetaAdmissibleFunction) :
    AnalyticOn ℂ
      (fun z => zetaCompletedExplicitFormulaPhi f z)
      Set.univ := by
  have hbase :
      AnalyticOn ℂ
        (fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z)
        Set.univ :=
    zetaLaplaceTransform_entire_of_compactSupport f
  have hphi :
      (fun z => zetaCompletedExplicitFormulaPhi f z) =
        (fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z) :=
    zetaCompletedExplicitFormulaPhi_eq_laplace f
  exact Eq.subst
    (motive := fun Φ : ℂ → ℂ => AnalyticOn ℂ Φ Set.univ)
    hphi.symm
    hbase

/-- Compact support of the admissible source gives differentiability of the completed
Laplace transform at every spectral parameter. -/
theorem zetaPhi_differentiableAt_of_compactSupport
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    DifferentiableAt ℂ
      (fun z => zetaCompletedExplicitFormulaPhi f z)
      z := by
  classical
  have hbase :
      DifferentiableAt ℂ
        (fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z)
        z :=
    Boundary.zetaLaplaceTransform_differentiableAt f z
  have hphi :
      (fun z => zetaCompletedExplicitFormulaPhi f z) =
        (fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z) :=
    zetaCompletedExplicitFormulaPhi_eq_laplace f
  exact Eq.subst
    (motive := fun Φ : ℂ → ℂ => DifferentiableAt ℂ Φ z)
    hphi.symm
    hbase

/-- Build the completed transform control package from supplied concrete strip constants. -/
def zetaPhiAnalyticControl_of_suppliedConstants
    (f : ZetaAdmissibleFunction)
    (C : ℝ → ℝ → ℕ → ℝ)
    (hCpos : ∀ (a b : ℝ) (N : ℕ), 0 < C a b N)
    (hCbound :
      ∀ (a b : ℝ) (N : ℕ) (z : ℂ),
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C a b N * (1 + ‖z.im‖) ^ (-(N : ℤ))) :
    ZetaPhiAnalyticControl f :=
  { entire_phi := zetaPhi_entire_of_compactSupport f
    differentiableAt_phi := fun z => zetaPhi_differentiableAt_of_compactSupport f z
    vertical_strip_rapid_decay :=
      fun a b N => ⟨C a b N, hCpos a b N, hCbound a b N⟩
    vertical_strip_rapid_decay_constant := C
    vertical_strip_rapid_decay_constant_pos := hCpos
    vertical_strip_rapid_decay_constant_bound := hCbound }

/-- Concrete completed-transform strip constants for autocorrelation probes. -/
structure ZetaPhiAutocorrelationConcreteControl where
  Cphi : ZetaAdmissibleFunction → ℝ → ℝ → ℕ → ℝ
  Cphi_pos :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ),
      0 < Cphi f a b N
  Cphi_bound :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) (z : ℂ),
      a ≤ z.re →
      z.re ≤ b →
      ‖zetaCompletedExplicitFormulaPhi
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) z‖
        ≤ Cphi f a b N * (1 + ‖z.im‖) ^ (-(N : ℤ))

/-- Concrete strip constants build transform-control packages on all
autocorrelation probes. -/
def zetaPhiAnalyticControl_autocorrelation_of_concreteConstants
    (Cphi : ZetaAdmissibleFunction → ℝ → ℝ → ℕ → ℝ)
    (hCphi_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ),
        0 < Cphi f a b N)
    (hCphi_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) (z : ℂ),
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) z‖
          ≤ Cphi f a b N * (1 + ‖z.im‖) ^ (-(N : ℤ))) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  fun f =>
    zetaPhiAnalyticControl_of_suppliedConstants
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (Cphi f)
      (hCphi_pos f)
      (hCphi_bound f)

/-- A named concrete transform-control surface builds transform-control
packages on all autocorrelation probes. -/
def zetaPhiAnalyticControl_autocorrelation_of_concreteControl
    (hPhiConcrete : ZetaPhiAutocorrelationConcreteControl) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  zetaPhiAnalyticControl_autocorrelation_of_concreteConstants
    hPhiConcrete.Cphi
    hPhiConcrete.Cphi_pos
    hPhiConcrete.Cphi_bound

/-- Analytic completed-transform packages expose the concrete strip constants
needed by autocorrelation consumers. -/
def zetaPhiAutocorrelationConcreteControl_of_analyticControl
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaPhiAutocorrelationConcreteControl :=
  { Cphi :=
      fun f a b N =>
        (hPhi f).vertical_strip_rapid_decay_constant a b N
    Cphi_pos :=
      fun f a b N =>
        (hPhi f).vertical_strip_rapid_decay_constant_pos a b N
    Cphi_bound :=
      fun f a b N z ha hb =>
        (hPhi f).vertical_strip_rapid_decay_constant_bound a b N z ha hb }

/-- Deterministic Paley-Wiener strip constant for the completed transform of an
autocorrelation probe. -/
noncomputable def zetaPhiAutocorrelationConcreteConstant
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) : ℝ :=
  zetaLaplaceTransform_supportInterval_decayConstant
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)
    (canonicalZetaPaleyWienerSupportInterval
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    a
    b
    N

/-- The deterministic autocorrelation completed-transform strip constant is
positive. -/
theorem zetaPhiAutocorrelationConcreteConstant_pos
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    0 < zetaPhiAutocorrelationConcreteConstant f a b N :=
  zetaLaplaceTransform_supportInterval_decayConstant_pos
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)
    (canonicalZetaPaleyWienerSupportInterval
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    a
    b
    N

/-- The deterministic autocorrelation completed-transform strip constant bounds
the completed transform on every vertical strip. -/
theorem zetaPhiAutocorrelationConcreteConstant_bound
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) (z : ℂ)
    (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) z‖
      ≤ zetaPhiAutocorrelationConcreteConstant f a b N *
          (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  let g : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let I : ZetaPaleyWienerSupportInterval g :=
    canonicalZetaPaleyWienerSupportInterval g
  let C : ℝ :=
    zetaLaplaceTransform_supportInterval_decayConstant g I a b N
  have hLaplace :
      zetaLaplaceTransformHasVerticalStripDecayConstant g a b N C :=
    And.intro
      (zetaLaplaceTransform_supportInterval_decayConstant_pos g I a b N)
      (zetaLaplaceTransform_supportInterval_decayConstant_bound g I a b N)
  have hPhi :
      0 < C ∧
        ∀ w : ℂ,
          a ≤ w.re →
          w.re ≤ b →
          ‖zetaCompletedExplicitFormulaPhi g w‖
            ≤ C * (1 + ‖w.im‖) ^ (-(N : ℤ)) :=
    Boundary.LFunctions.zetaPhi_hasVerticalStripDecayConstant_of_laplace
      g a b N C hLaplace
  exact hPhi.2 z ha hb

/-- Canonical concrete completed-transform control on all autocorrelation
probes, with constants supplied by the Paley-Wiener/Laplace owner. -/
def zetaPhiAutocorrelationConcreteControl_owner :
    ZetaPhiAutocorrelationConcreteControl :=
  { Cphi := zetaPhiAutocorrelationConcreteConstant
    Cphi_pos := zetaPhiAutocorrelationConcreteConstant_pos
    Cphi_bound := zetaPhiAutocorrelationConcreteConstant_bound }

/-- Vertical-strip rapid decay of the completed transform, transported from the
Paley-Wiener integration-by-parts estimate for the admissible source. -/
theorem zetaPhi_verticalStripRapidDecay
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact zetaPhi_verticalStripRapidDecay_of_admissible f a b N

/-- The transform package is the owner-level input for contour estimates. -/
def ZetaPhiAnalyticControlPackage (f : ZetaAdmissibleFunction) : Type :=
  ZetaPhiAnalyticControl f

/-- The transform package is exactly the analytic control data. -/
def ZetaPhiAnalyticControlPackage_eq
    (f : ZetaAdmissibleFunction) :
    ZetaPhiAnalyticControlPackage f = ZetaPhiAnalyticControl f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
