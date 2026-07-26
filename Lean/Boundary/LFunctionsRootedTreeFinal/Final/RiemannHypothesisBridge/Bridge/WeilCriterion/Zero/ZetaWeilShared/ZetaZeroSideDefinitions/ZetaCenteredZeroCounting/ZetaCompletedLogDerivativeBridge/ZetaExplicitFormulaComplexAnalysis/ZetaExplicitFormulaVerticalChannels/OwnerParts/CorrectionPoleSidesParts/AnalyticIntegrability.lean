import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSidesParts.Core

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The left vertical side never meets the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hlt : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 1 := by
    have hpos : 0 < (F.rectangle T).c :=
      F.c_pos
    exact Eq.symm hre ▸ sub_lt_self (1 : ℝ) hpos
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_lt hlt) hre_one

/-- The shifted completed transform is continuous along the right vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhi.comp hpath

/-- The shifted completed transform is continuous along the left vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhi.comp hpath

/-- Right vertical archimedean-channel integrability on a finite height interval,
with regularity supplied by the contour boundary-avoidance certificate. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaRightPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inl ⟨t, ht, Eq.refl _⟩
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x))
          t :=
      ContinuousAt.comp'
        (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
          s hs0 hs1 hΛ hΓ)
        hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Left vertical archimedean-channel integrability on a finite height interval,
with regularity supplied by the contour boundary-avoidance certificate. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inr (Or.inl ⟨t, ht, Eq.refl _⟩)
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x))
          t :=
      ContinuousAt.comp'
        (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
          s hs0 hs1 hΛ hΓ)
        hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Right vertical correction-channel integrability for the original correction
log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionRightVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden0 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      hpath
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.div hden0
        (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc

/-- Left vertical correction-channel integrability for the original correction
log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden0 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      hpath
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.div hden0
        (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
