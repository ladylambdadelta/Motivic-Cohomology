import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
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

/-- Analytic control data for the explicit-formula transform `Φ_f`. -/
structure ZetaPhiAnalyticControl (f : ZetaAdmissibleFunction) where
  /-- `Φ_f` is entire. -/
  entire_phi : AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ
  /-- `Φ_f` is differentiable at every point. -/
  differentiableAt_phi : ∀ z : ℂ,
    DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z
  /-- `Φ_f` has vertical-strip rapid decay. -/
  vertical_strip_rapid_decay :
    ∀ (a b : ℝ) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖zetaCompletedExplicitFormulaPhi f z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))
  /-- A concrete rapid-decay constant for `Φ_f` on each vertical strip. -/
  vertical_strip_rapid_decay_constant : ℝ → ℝ → ℕ → ℝ
  /-- The concrete vertical-strip rapid-decay constant is positive. -/
  vertical_strip_rapid_decay_constant_pos :
    ∀ (a b : ℝ) (N : ℕ),
      0 < vertical_strip_rapid_decay_constant a b N
  /-- The concrete vertical-strip rapid-decay constant bounds `Φ_f` on the strip. -/
  vertical_strip_rapid_decay_constant_bound :
    ∀ (a b : ℝ) (N : ℕ) (z : ℂ),
      a ≤ z.re →
      z.re ≤ b →
      ‖zetaCompletedExplicitFormulaPhi f z‖
        ≤ vertical_strip_rapid_decay_constant a b N *
          (1 + ‖z.im‖) ^ (-(N : ℤ))

/-- The analytic control package exposes pointwise differentiability. -/
theorem ZetaPhiAnalyticControl.differentiableAt
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f) (z : ℂ) :
    DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z := by
  exact h.differentiableAt_phi z

/-- The analytic control package exposes the entireity statement. -/
theorem ZetaPhiAnalyticControl.entire
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f) :
    AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ := by
  exact h.entire_phi

/-- The analytic control package exposes the vertical-strip decay bound. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecay
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact h.vertical_strip_rapid_decay a b N

/-- The recorded rapid-decay constant for `Φ_f` on a vertical strip. -/
def ZetaPhiAnalyticControl.verticalStripRapidDecayConstant
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  h.vertical_strip_rapid_decay_constant a b N

/-- The recorded vertical-strip rapid-decay constant is positive. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecayConstant_pos
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) :
    0 < h.verticalStripRapidDecayConstant a b N := by
  exact h.vertical_strip_rapid_decay_constant_pos a b N

/-- The recorded vertical-strip rapid-decay constant bounds `Φ_f` on the strip. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecayConstant_bound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (z : ℂ)
    (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f z‖
      ≤ h.verticalStripRapidDecayConstant a b N *
        (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact h.vertical_strip_rapid_decay_constant_bound a b N z ha hb

/-- `Φ_f` is differentiable along the right contour edge whenever the control package is present. -/
theorem ZetaPhiAnalyticControl.differentiableAt_rightPath
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath r t) := by
  exact h.differentiableAt_phi _

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
    match h.verticalStripRapidDecay a b N with
    | ⟨C, hC, hbound⟩ =>
        ⟨C, hC, hbound (zetaCompletedExplicitFormulaRightPath r t) ha hb⟩

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
    match h.verticalStripRapidDecay a b N with
    | ⟨C, hC, hbound⟩ =>
        ⟨C, hC, hbound (zetaCompletedExplicitFormulaTopPath r x) ha hb⟩

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
    match h.verticalStripRapidDecay a b N with
    | ⟨C, hC, hbound⟩ =>
        ⟨C, hC, hbound (zetaCompletedExplicitFormulaBottomPath r x) ha hb⟩

/-- Compact support of the admissible source gives entireity of the completed Laplace
transform. -/
theorem zetaLaplaceTransform_entire_of_compactSupport
    (f : ZetaAdmissibleFunction) :
    [∀ t : ℝ, Decidable (t ∈ tsupport f.toZetaTestFunction')] →
    AnalyticOn ℂ
      (fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z)
      Set.univ := by
  intro _inst
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
    [∀ t : ℝ, Decidable (t ∈ tsupport f.toZetaTestFunction')] →
    AnalyticOn ℂ
      (fun z => zetaCompletedExplicitFormulaPhi f z)
      Set.univ := by
  intro _inst
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
    [∀ t : ℝ, Decidable (t ∈ tsupport f.toZetaTestFunction')] →
    DifferentiableAt ℂ
      (fun z => zetaCompletedExplicitFormulaPhi f z)
      z := by
  intro _inst
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
    [∀ t : ℝ, Decidable (t ∈ tsupport f.toZetaTestFunction')]
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

/-- Owner gap: vertical-strip rapid decay of the completed transform.  This is the
analytic integration-by-parts estimate for the compactly supported admissible source. -/
theorem zetaPhi_verticalStripRapidDecay_ownerGap
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact zetaPhi_verticalStripRapidDecay_of_admissible f a b N

/-- The canonical rapid-decay constant selected from admissible Paley-Wiener decay. -/
noncomputable def zetaPhiVerticalStripRapidDecayConstant
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) : ℝ :=
  Classical.choose (zetaPhi_verticalStripRapidDecay_ownerGap f a b N)

/-- The selected admissible Paley-Wiener rapid-decay constant is positive. -/
theorem zetaPhiVerticalStripRapidDecayConstant_pos
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    0 < zetaPhiVerticalStripRapidDecayConstant f a b N := by
  exact (Classical.choose_spec
    (zetaPhi_verticalStripRapidDecay_ownerGap f a b N)).1

/-- The selected admissible Paley-Wiener constant gives the requested strip bound. -/
theorem zetaPhiVerticalStripRapidDecayConstant_bound
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) (z : ℂ)
    (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f z‖ ≤
      zetaPhiVerticalStripRapidDecayConstant f a b N *
        (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact (Classical.choose_spec
    (zetaPhi_verticalStripRapidDecay_ownerGap f a b N)).2 z ha hb

/-- Every admissible probe carries the canonical completed-transform control package. -/
noncomputable def zetaPhiAnalyticControl_of_admissible
    (f : ZetaAdmissibleFunction) : ZetaPhiAnalyticControl f := by
  letI hdecidable : ∀ t : ℝ,
      Decidable (t ∈ tsupport f.toZetaTestFunction') :=
    fun t : ℝ => Classical.propDecidable (t ∈ tsupport f.toZetaTestFunction')
  exact zetaPhiAnalyticControl_of_suppliedConstants
    f
    (zetaPhiVerticalStripRapidDecayConstant f)
    (zetaPhiVerticalStripRapidDecayConstant_pos f)
    (zetaPhiVerticalStripRapidDecayConstant_bound f)

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
