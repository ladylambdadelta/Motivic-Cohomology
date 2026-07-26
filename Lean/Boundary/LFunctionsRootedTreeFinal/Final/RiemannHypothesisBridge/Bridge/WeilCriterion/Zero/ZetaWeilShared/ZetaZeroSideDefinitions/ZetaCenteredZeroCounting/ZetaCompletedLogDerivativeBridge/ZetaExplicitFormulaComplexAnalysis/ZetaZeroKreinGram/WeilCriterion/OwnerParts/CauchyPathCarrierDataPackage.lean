import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathPacketDataBoundaryIdentification
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.CarrierFactorData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.VariableCauchyPathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledHorizontalBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.FinalCommonLimitCanonicalPathCauchyDataCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SuppliedScheduleCarrierDataPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner

/-!
# Packaged carrier Cauchy data

This file owns the narrow package of carrier-level Cauchy estimates used in the
scheduled horizontal path lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Carrier-level Cauchy estimates for the canonical scheduled horizontal
carrier, split into the zeta-side and inverse-Gamma factors. -/
structure CanonicalScheduledCarrierCauchyData
    (K : ZetaAdmissibleFunction → ℕ) where
  zetaRadius : ∀ f : ZetaAdmissibleFunction, ℝ
  zetaAmplitude : ∀ f : ZetaAdmissibleFunction, ℝ
  zetaValueLower : ∀ f : ZetaAdmissibleFunction, ℝ
  gammaRadius : ∀ f : ZetaAdmissibleFunction, ℝ
  gammaAmplitude : ∀ f : ZetaAdmissibleFunction, ℝ
  gammaValueLower : ∀ f : ZetaAdmissibleFunction, ℝ
  zetaRadius_pos :
    ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f
  zetaAmplitude_pos :
    ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f
  zetaValueLower_pos :
    ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f
  gammaRadius_pos :
    ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f
  gammaAmplitude_pos :
    ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f
  gammaValueLower_pos :
    ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f
  zetaDiffCont :
    ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
      z ∈
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
          .carrier →
      DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
        (Metric.ball z (zetaRadius f))
  gammaDiffCont :
    ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
      z ∈
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
          .carrier →
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z (gammaRadius f))
  zetaSphereBound :
    ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
      z ∈
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
          .carrier →
      ∀ w : ℂ,
        w ∈ Metric.sphere z (zetaRadius f) →
        ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
          zetaAmplitude f * (1 + ‖z.im‖) ^ K f
  gammaSphereBound :
    ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
      z ∈
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
          .carrier →
      ∀ w : ℂ,
        w ∈ Metric.sphere z (gammaRadius f) →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          gammaAmplitude f * (1 + ‖z.im‖) ^ K f
  zetaValueLower_bound :
    ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
      z ∈
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
          .carrier →
      zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖
  gammaValueLower_bound :
    ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
      z ∈
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
          .carrier →
      gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖

/-- The zeta-side carrier package restricts to scheduled path Cauchy data. -/
def CanonicalScheduledCarrierCauchyData.zetaPathData
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
      f (K f) :=
  ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData.ofCarrierCauchyData
    f
    (K f)
    (data.zetaRadius f)
    (data.zetaAmplitude f)
    (data.zetaValueLower f)
    (data.zetaRadius_pos f)
    (data.zetaAmplitude_pos f)
    (data.zetaValueLower_pos f)
    (data.zetaDiffCont f)
    (data.zetaSphereBound f)
    (data.zetaValueLower_bound f)

/-- The inverse-Gamma carrier package restricts to scheduled path Cauchy data. -/
def CanonicalScheduledCarrierCauchyData.gammaPathData
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
      f (K f) :=
  ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData.ofCarrierCauchyData
    f
    (K f)
    (data.gammaRadius f)
    (data.gammaAmplitude f)
    (data.gammaValueLower f)
    (data.gammaRadius_pos f)
    (data.gammaAmplitude_pos f)
    (data.gammaValueLower_pos f)
    (data.gammaDiffCont f)
    (data.gammaSphereBound f)
    (data.gammaValueLower_bound f)

def CanonicalScheduledCarrierCauchyData.pathData
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K) :
    CanonicalScheduledPathCauchyData K :=
  CanonicalScheduledPathCauchyData.ofComponentData
    K
    (fun f => data.zetaPathData f)
    (fun f => data.gammaPathData f)

def CanonicalScheduledCarrierCauchyData.zetaVariablePathData
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData f (K f) :=
  fun f =>
    ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData.of_uniform
      (data.pathData).zetaData f

def CanonicalScheduledCarrierCauchyData.gammaVariablePathData
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData f (K f) :=
  fun f =>
    ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData.of_uniform
      (data.pathData).gammaData f

theorem canonicalScheduledCarrierCauchyData_variablePathData_owner
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K) :
    (∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
        f (K f)) ∧
    (∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
        f (K f)) :=
  let pathData := data.pathData
  ⟨
    fun f => ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData.of_uniform
      pathData.zetaData f,
    fun f => ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData.of_uniform
      pathData.gammaData f⟩

def CanonicalScheduledCarrierCauchyData.variableHorizontalBounds
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f :=
  let variableData := canonicalScheduledCarrierCauchyData_variablePathData_owner data
  fun f =>
    ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.of_variableCauchyPathData
      f
      (K f)
      ((variableData.1) f)
      ((variableData.2) f)

def CanonicalScheduledCarrierCauchyData.of_pathData
    {K : ZetaAdmissibleFunction → ℕ}
    (zetaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData f (K f))
    (gammaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData f (K f)) :
    CanonicalScheduledCarrierCauchyData K :=
  { zetaRadius := fun f => (zetaData f).radius
    zetaAmplitude := fun f => (zetaData f).amplitude
    zetaValueLower := fun f => (zetaData f).valueLower
    gammaRadius := fun f => (gammaData f).radius
    gammaAmplitude := fun f => (gammaData f).amplitude
    gammaValueLower := fun f => (gammaData f).valueLower
    zetaRadius_pos := fun f => (zetaData f).radius_pos
    zetaAmplitude_pos := fun f => (zetaData f).amplitude_pos
    zetaValueLower_pos := fun f => (zetaData f).valueLower_pos
    gammaRadius_pos := fun f => (gammaData f).radius_pos
    gammaAmplitude_pos := fun f => (gammaData f).amplitude_pos
    gammaValueLower_pos := fun f => (gammaData f).valueLower_pos
    zetaDiffCont := fun f z hz =>
      match zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases f z hz with
      | Or.inl htop =>
          Exists.elim htop (fun u hu =>
            Exists.elim hu (fun x hx =>
              Eq.subst (motive := fun w : ℂ =>
                DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
                  (Metric.ball w (zetaData f).radius))
                hx.2.symm ((zetaData f).top_diffCont u x hx.1)))
      | Or.inr hbottom =>
          Exists.elim hbottom (fun u hu =>
            Exists.elim hu (fun x hx =>
              Eq.subst (motive := fun w : ℂ =>
                DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
                  (Metric.ball w (zetaData f).radius))
                hx.2.symm ((zetaData f).bottom_diffCont u x hx.1)))
    gammaDiffCont := fun f z hz =>
      match zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases f z hz with
      | Or.inl htop =>
          Exists.elim htop (fun u hu =>
            Exists.elim hu (fun x hx =>
              Eq.subst (motive := fun w : ℂ =>
                DiffContOnCl ℂ (fun v : ℂ => (Complex.Gammaℝ v)⁻¹)
                  (Metric.ball w (gammaData f).radius))
                hx.2.symm ((gammaData f).top_diffCont u x hx.1)))
      | Or.inr hbottom =>
          Exists.elim hbottom (fun u hu =>
            Exists.elim hu (fun x hx =>
              Eq.subst (motive := fun w : ℂ =>
                DiffContOnCl ℂ (fun v : ℂ => (Complex.Gammaℝ v)⁻¹)
                  (Metric.ball w (gammaData f).radius))
                hx.2.symm ((gammaData f).bottom_diffCont u x hx.1)))
    zetaSphereBound := fun f z hz w hw =>
      match zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases f z hz with
      | Or.inl htop =>
          Exists.elim htop (fun u hu => Exists.elim hu (fun x hx =>
            let hpath := (zetaData f).top_sphereBound u x hx.1 w hw
            let hshape :
                (zetaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K f =
                  (zetaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaTopPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              congrArg (fun r : ℝ => (zetaData f).amplitude * (1 + r) ^ K f)
                (zetaCompletedExplicitFormulaTopPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).symm
            let hbound :
                ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
                  (zetaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaTopPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              Eq.subst (motive := fun q : ℝ => ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤ q)
                hshape hpath
            Eq.subst (motive := fun v : ℂ =>
              ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
                (zetaData f).amplitude * (1 + ‖v.im‖) ^ K f)
              hx.2.symm hbound)))
      | Or.inr hbottom =>
          Exists.elim hbottom (fun u hu => Exists.elim hu (fun x hx =>
            let hpath := (zetaData f).bottom_sphereBound u x hx.1 w hw
            let hshape :
                (zetaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K f =
                  (zetaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaBottomPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              congrArg (fun r : ℝ => (zetaData f).amplitude * (1 + r) ^ K f)
                (zetaCompletedExplicitFormulaBottomPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).symm
            let hbound :
                ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
                  (zetaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaBottomPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              Eq.subst (motive := fun q : ℝ => ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤ q)
                hshape hpath
            Eq.subst (motive := fun v : ℂ =>
              ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
                (zetaData f).amplitude * (1 + ‖v.im‖) ^ K f)
              hx.2.symm hbound)))
    gammaSphereBound := fun f z hz w hw =>
      match zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases f z hz with
      | Or.inl htop =>
          Exists.elim htop (fun u hu => Exists.elim hu (fun x hx =>
            let hpath := (gammaData f).top_sphereBound u x hx.1 w hw
            let hshape :
                (gammaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K f =
                  (gammaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaTopPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              congrArg (fun r : ℝ => (gammaData f).amplitude * (1 + r) ^ K f)
                (zetaCompletedExplicitFormulaTopPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).symm
            let hbound :
                ‖(Complex.Gammaℝ w)⁻¹‖ ≤
                  (gammaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaTopPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              Eq.subst (motive := fun q : ℝ => ‖(Complex.Gammaℝ w)⁻¹‖ ≤ q)
                hshape hpath
            Eq.subst (motive := fun v : ℂ =>
              ‖(Complex.Gammaℝ w)⁻¹‖ ≤
                (gammaData f).amplitude * (1 + ‖v.im‖) ^ K f)
              hx.2.symm hbound)))
      | Or.inr hbottom =>
          Exists.elim hbottom (fun u hu => Exists.elim hu (fun x hx =>
            let hpath := (gammaData f).bottom_sphereBound u x hx.1 w hw
            let hshape :
                (gammaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K f =
                  (gammaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaBottomPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              congrArg (fun r : ℝ => (gammaData f).amplitude * (1 + r) ^ K f)
                (zetaCompletedExplicitFormulaBottomPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).symm
            let hbound :
                ‖(Complex.Gammaℝ w)⁻¹‖ ≤
                  (gammaData f).amplitude *
                    (1 + ‖(zetaCompletedExplicitFormulaBottomPath
                      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ K f :=
              Eq.subst (motive := fun q : ℝ => ‖(Complex.Gammaℝ w)⁻¹‖ ≤ q)
                hshape hpath
            Eq.subst (motive := fun v : ℂ =>
              ‖(Complex.Gammaℝ w)⁻¹‖ ≤
                (gammaData f).amplitude * (1 + ‖v.im‖) ^ K f)
              hx.2.symm hbound)))
    zetaValueLower_bound := fun f z hz =>
      match zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases f z hz with
      | Or.inl htop => Exists.elim htop (fun u hu => Exists.elim hu (fun x hx =>
          Eq.subst (motive := fun v : ℂ => (zetaData f).valueLower ≤ ‖ZetaAdmissibleFunction.zetaSideFactor v‖)
            hx.2.symm ((zetaData f).top_valueLower u x hx.1)))
      | Or.inr hbottom => Exists.elim hbottom (fun u hu => Exists.elim hu (fun x hx =>
          Eq.subst (motive := fun v : ℂ => (zetaData f).valueLower ≤ ‖ZetaAdmissibleFunction.zetaSideFactor v‖)
            hx.2.symm ((zetaData f).bottom_valueLower u x hx.1)))
    gammaValueLower_bound := fun f z hz =>
      match zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases f z hz with
      | Or.inl htop => Exists.elim htop (fun u hu => Exists.elim hu (fun x hx =>
          Eq.subst (motive := fun v : ℂ => (gammaData f).valueLower ≤ ‖(Complex.Gammaℝ v)⁻¹‖)
            hx.2.symm ((gammaData f).top_valueLower u x hx.1)))
      | Or.inr hbottom => Exists.elim hbottom (fun u hu => Exists.elim hu (fun x hx =>
          Eq.subst (motive := fun v : ℂ => (gammaData f).valueLower ≤ ‖(Complex.Gammaℝ v)⁻¹‖)
              hx.2.symm ((gammaData f).bottom_valueLower u x hx.1))) }

theorem canonicalScheduledCarrierCauchyData_of_pathData_owner
    {K : ZetaAdmissibleFunction → ℕ}
    (zetaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData f (K f))
    (gammaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData f (K f)) :
    CanonicalScheduledCarrierCauchyData K :=
  CanonicalScheduledCarrierCauchyData.of_pathData zetaData gammaData

/-- Canonical carrier Cauchy data is the supplied-schedule package specialized
to the canonical cofinal schedule. -/
def CanonicalScheduledCarrierCauchyData.toSuppliedScheduleData
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyData
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule
        f)
      (K f) :=
  { zetaRadius := data.zetaRadius f
    zetaAmplitude := data.zetaAmplitude f
    zetaValueLower := data.zetaValueLower f
    gammaRadius := data.gammaRadius f
    gammaAmplitude := data.gammaAmplitude f
    gammaValueLower := data.gammaValueLower f
    zetaRadius_pos := data.zetaRadius_pos f
    zetaAmplitude_pos := data.zetaAmplitude_pos f
    zetaValueLower_pos := data.zetaValueLower_pos f
    gammaRadius_pos := data.gammaRadius_pos f
    gammaAmplitude_pos := data.gammaAmplitude_pos f
    gammaValueLower_pos := data.gammaValueLower_pos f
    zetaDiffCont := data.zetaDiffCont f
    gammaDiffCont := data.gammaDiffCont f
    zetaSphereBound := data.zetaSphereBound f
    gammaSphereBound := data.gammaSphereBound f
    zetaValueLower_bound := data.zetaValueLower_bound f
    gammaValueLower_bound := data.gammaValueLower_bound f }

/-- Packaged carrier Cauchy data also gives the completed-log-derivative factor
bound data on the canonical scheduled carrier. -/
def CanonicalScheduledCarrierCauchyData.factorBoundData
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction)
    (separated :
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
        f).HasPositiveSingularSeparation) :
    ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
        f) :=
  ((data.toSuppliedScheduleData f).toLogDerivData).factorBoundData
    separated

/-- Packaged carrier Cauchy data and separation construct the scheduled
autocorrelation analytic package. -/
def CanonicalScheduledCarrierCauchyData.scheduledAnalyticPackage
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (separated :
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
        f).HasPositiveSingularSeparation) :
    ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  (data.toSuppliedScheduleData f).scheduledAnalyticPackage
    hPhi
    separated

/-- Packaged carrier Cauchy data and separation construct the scheduled
polynomial autocorrelation analytic package. -/
def CanonicalScheduledCarrierCauchyData.scheduledPolynomialPackage
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (separated :
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
        f).HasPositiveSingularSeparation) :
    ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  (data.toSuppliedScheduleData f).scheduledPolynomialPackage
    hPhi
    separated

/-- Packaged canonical carrier Cauchy data gives the supplied-schedule family
specialized to the canonical cofinal height schedule. -/
def CanonicalScheduledCarrierCauchyData.toSuppliedScheduleFamily
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily :=
  { schedule :=
      fun f =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule
          f
    degree := K
    carrierData := fun f => data.toSuppliedScheduleData f
    separated := separated
    phiControl := hPhi }

/-- Packaged carrier Cauchy data and affine packet data give raw Weil
positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_packetData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetData_traceBessel_owner
    K
    carrierData.pathData.zetaData
    carrierData.pathData.gammaData
    packetData

/-- Packaged carrier Cauchy data gives scheduled polynomial horizontal
bounds. -/
def CanonicalScheduledCarrierCauchyData.horizontalBounds
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f :=
  ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.of_cauchyPathData
    f
    (K f)
    (data.pathData).zetaData f
    (data.pathData).gammaData f

theorem canonicalScheduledCarrierCauchyData_horizontalBounds_owner
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K)
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f :=
  (data.variableHorizontalBounds f)

/-- The carrier package is the owner-level source of the horizontal polynomial
bounds consumed by the final common-limit theorem. -/
def CanonicalScheduledCarrierCauchyData.horizontalBoundsFamily
    {K : ZetaAdmissibleFunction → ℕ}
    (data : CanonicalScheduledCarrierCauchyData K) :
  ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f :=
  fun f => canonicalScheduledCarrierCauchyData_horizontalBounds_owner data f

/-- Packaged carrier Cauchy data and affine packet data give raw Weil
positivity through the horizontal-bound package. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_horizontalBounds_packetData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_packetData_traceBessel_owner
    (fun f => carrierData.horizontalBounds f)
    packetData

/-- Packaged carrier Cauchy data and global factor controls give raw Weil
positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_globalFactorControls_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_horizontalBounds_packetData_traceBessel_owner
    K
    carrierData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_globalFactorControls_owner
        f
        hZetaSide
        hInverseGamma)

end

end LFunctions
end Boundary
