import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.CarrierFactorData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.FactorPathBounds

/-!
# Supplied-schedule carrier Cauchy data

This owner part keeps the quantitative horizontal carrier estimates attached to
a supplied cofinal schedule.  It is the schedule-parametric form needed before
specializing to any canonical schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Carrier-level Cauchy estimates for a supplied autocorrelation cofinal
schedule, split into the zeta-side and inverse-Gamma factors. -/
structure SuppliedScheduleCarrierCauchyData
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (K : ℕ) where
  zetaRadius : ℝ
  zetaAmplitude : ℝ
  zetaValueLower : ℝ
  gammaRadius : ℝ
  gammaAmplitude : ℝ
  gammaValueLower : ℝ
  zetaRadius_pos : 0 < zetaRadius
  zetaAmplitude_pos : 0 < zetaAmplitude
  zetaValueLower_pos : 0 < zetaValueLower
  gammaRadius_pos : 0 < gammaRadius
  gammaAmplitude_pos : 0 < gammaAmplitude
  gammaValueLower_pos : 0 < gammaValueLower
  zetaDiffCont :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball z zetaRadius)
  gammaDiffCont :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z gammaRadius)
  zetaSphereBound :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      ∀ w : ℂ,
        w ∈ Metric.sphere z zetaRadius →
        ‖zetaSideFactor w‖ ≤
          zetaAmplitude * (1 + ‖z.im‖) ^ K
  gammaSphereBound :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      ∀ w : ℂ,
        w ∈ Metric.sphere z gammaRadius →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          gammaAmplitude * (1 + ‖z.im‖) ^ K
  zetaValueLower_bound :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      zetaValueLower ≤ ‖zetaSideFactor z‖
  gammaValueLower_bound :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      gammaValueLower ≤ ‖(Complex.Gammaℝ z)⁻¹‖

/-! The direct schedule package records the logarithmic-derivative estimates
actually consumed downstream.  It is separate from the legacy Cauchy package
because reciprocal Gamma has exponential vertical magnitude growth. -/

/-- Direct logarithmic-derivative bounds on a supplied scheduled carrier. -/
structure SuppliedScheduleCarrierLogDerivData
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (K : ℕ) where
  zetaConstant : ℝ
  gammaConstant : ℝ
  zetaConstant_pos : 0 < zetaConstant
  gammaConstant_pos : 0 < gammaConstant
  zetaBound :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      ‖zetaSideNegLogDeriv z‖ ≤
        zetaConstant * (1 + ‖z.im‖) ^ K
  gammaBound :
    ∀ z : ℂ,
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        gammaConstant * (1 + ‖z.im‖) ^ K

def SuppliedScheduleCarrierCauchyData.toLogDerivData
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ}
    (data : SuppliedScheduleCarrierCauchyData f schedule K) :
    SuppliedScheduleCarrierLogDerivData f schedule K :=
  { zetaConstant := (data.zetaAmplitude / data.zetaRadius) / data.zetaValueLower
    gammaConstant := (data.gammaAmplitude / data.gammaRadius) / data.gammaValueLower
    zetaConstant_pos :=
      div_pos
        (div_pos data.zetaAmplitude_pos data.zetaRadius_pos)
        data.zetaValueLower_pos
    gammaConstant_pos :=
      div_pos
        (div_pos data.gammaAmplitude_pos data.gammaRadius_pos)
        data.gammaValueLower_pos
    zetaBound := by
      intro z hz
      exact zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
        z K z.im data.zetaRadius data.zetaAmplitude data.zetaValueLower
        data.zetaRadius_pos
        (data.zetaDiffCont z hz)
        (data.zetaSphereBound z hz)
        (data.zetaValueLower_bound z hz)
    gammaBound := by
      intro z hz
      exact inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
        z K z.im data.gammaRadius data.gammaAmplitude data.gammaValueLower
        data.gammaRadius_pos
        (data.gammaDiffCont z hz)
        (data.gammaSphereBound z hz)
        (data.gammaValueLower_bound z hz) }

theorem SuppliedScheduleCarrierLogDerivData.zetaNormalizedBound
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ} (data : SuppliedScheduleCarrierLogDerivData f schedule K)
    {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).carrier) :
    ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ K ≤ data.zetaConstant := by
  have hheight : 0 < (1 + ‖z.im‖) ^ K :=
    pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg z.im)) K
  exact (div_le_iff₀ hheight).mpr (data.zetaBound z hz)

theorem SuppliedScheduleCarrierLogDerivData.gammaNormalizedBound
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ} (data : SuppliedScheduleCarrierLogDerivData f schedule K)
    {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).carrier) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ /
      (1 + ‖z.im‖) ^ K ≤ data.gammaConstant := by
  have hheight : 0 < (1 + ‖z.im‖) ^ K :=
    pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg z.im)) K
  exact (div_le_iff₀ hheight).mpr (data.gammaBound z hz)

theorem SuppliedScheduleCarrierLogDerivData.zetaNormalizedBddAbove
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ} (data : SuppliedScheduleCarrierLogDerivData f schedule K) :
    BddAbove
      ((fun z : ℂ =>
          ‖zetaSideNegLogDeriv z‖ / (1 + ‖z.im‖) ^ K) ''
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier) :=
  Exists.intro data.zetaConstant
    (fun y hy =>
      Exists.elim hy
        (fun z hz =>
          Eq.subst
            (motive := fun value : ℝ => value ≤ data.zetaConstant)
            hz.2
            (data.zetaNormalizedBound hz.1)))

theorem SuppliedScheduleCarrierLogDerivData.gammaNormalizedBddAbove
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ} (data : SuppliedScheduleCarrierLogDerivData f schedule K) :
    BddAbove
      ((fun z : ℂ =>
          ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
              (Complex.Gammaℝ z)⁻¹‖ /
            (1 + ‖z.im‖) ^ K) ''
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule).carrier) :=
  Exists.intro data.gammaConstant
    (fun y hy =>
      Exists.elim hy
        (fun z hz =>
          Eq.subst
            (motive := fun value : ℝ => value ≤ data.gammaConstant)
            hz.2
            (data.gammaNormalizedBound hz.1)))

/-- Direct scheduled logarithmic-derivative data gives factor-bound data. -/
def SuppliedScheduleCarrierLogDerivData.factorBoundData
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ}
    (data : SuppliedScheduleCarrierLogDerivData f schedule K)
    (separated :
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).HasPositiveSingularSeparation) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule) :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofLogDerivBounds
    (CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofConstants
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule)
      separated
      (fun _ : ℕ => data.zetaConstant)
      (fun _ : ℕ => data.zetaConstant_pos)
      (fun _ : ℕ => data.zetaBound))
    (CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofLogDerivBound
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule)
      separated
      (fun _ : ℕ => data.gammaConstant)
      (fun _ : ℕ => data.gammaConstant_pos)
      (fun _ : ℕ => data.gammaBound))

/-- Direct scheduled logarithmic-derivative data constructs the scheduled
autocorrelation analytic package. -/
def SuppliedScheduleCarrierLogDerivData.scheduledAnalyticPackage
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ}
    (data : SuppliedScheduleCarrierLogDerivData f schedule K)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (separated :
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).HasPositiveSingularSeparation) :
    ExplicitFormulaScheduledFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    schedule
    hPhi
    ((data.toLogDerivData).factorBoundData separated)

/-- Direct scheduled logarithmic-derivative data constructs the scheduled
polynomial autocorrelation analytic package. -/
def SuppliedScheduleCarrierLogDerivData.scheduledPolynomialPackage
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ}
    (data : SuppliedScheduleCarrierLogDerivData f schedule K)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (separated :
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).HasPositiveSingularSeparation) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    schedule
    hPhi
    ((data.toLogDerivData).factorBoundData separated)

/-- Supplied-schedule carrier Cauchy data gives factor-bound data on that
scheduled carrier. -/
def SuppliedScheduleCarrierCauchyData.factorBoundData
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ}
    (data : SuppliedScheduleCarrierCauchyData f schedule K)
    (separated :
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).HasPositiveSingularSeparation) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule) :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofCauchyLogDerivative
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
      f schedule)
    separated
    (fun N : ℕ => data.zetaRadius)
    (fun N : ℕ => data.zetaAmplitude)
    (fun N : ℕ => data.zetaValueLower)
    (fun N : ℕ => data.gammaRadius)
    (fun N : ℕ => data.gammaAmplitude)
    (fun N : ℕ => data.gammaValueLower)
    (fun N : ℕ => data.zetaRadius_pos)
    (fun N : ℕ => data.zetaAmplitude_pos)
    (fun N : ℕ => data.zetaValueLower_pos)
    (fun N : ℕ => data.gammaRadius_pos)
    (fun N : ℕ => data.gammaAmplitude_pos)
    (fun N : ℕ => data.gammaValueLower_pos)
    (fun N : ℕ => data.zetaDiffCont)
    (fun N : ℕ => data.zetaSphereBound)
    (fun N : ℕ => data.zetaValueLower_bound)
    (fun N : ℕ => data.gammaDiffCont)
    (fun N : ℕ => data.gammaSphereBound)
    (fun N : ℕ => data.gammaValueLower_bound)

/-- Supplied-schedule carrier Cauchy data constructs the scheduled
autocorrelation analytic package. -/
def SuppliedScheduleCarrierCauchyData.scheduledAnalyticPackage
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ}
    (data : SuppliedScheduleCarrierCauchyData f schedule K)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (separated :
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).HasPositiveSingularSeparation) :
    ExplicitFormulaScheduledFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    schedule
    hPhi
    (data.factorBoundData separated)

/-- Supplied-schedule carrier Cauchy data constructs the scheduled polynomial
autocorrelation analytic package. -/
def SuppliedScheduleCarrierCauchyData.scheduledPolynomialPackage
    {f : ZetaAdmissibleFunction}
    {schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)}
    {K : ℕ}
    (data : SuppliedScheduleCarrierCauchyData f schedule K)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (separated :
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).HasPositiveSingularSeparation) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    schedule
    hPhi
    (data.factorBoundData separated)

/-- Family-level quantitative carrier package for all autocorrelation seeds. -/
structure SuppliedScheduleCarrierCauchyFamily where
  schedule :
    ∀ f : ZetaAdmissibleFunction,
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
  degree : ZetaAdmissibleFunction → ℕ
  carrierData :
    ∀ f : ZetaAdmissibleFunction,
      SuppliedScheduleCarrierCauchyData f (schedule f) (degree f)
  separated :
    ∀ f : ZetaAdmissibleFunction,
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f (schedule f)).HasPositiveSingularSeparation
  phiControl :
    ∀ f : ZetaAdmissibleFunction,
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f)

def SuppliedScheduleCarrierCauchyFamily.ofCanonicalSchedule
    (degree : ZetaAdmissibleFunction → ℕ)
    (carrierData :
      ∀ f : ZetaAdmissibleFunction,
        SuppliedScheduleCarrierCauchyData
          f
          (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
          (degree f))
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (phiControl :
      ∀ f : ZetaAdmissibleFunction,
        ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    SuppliedScheduleCarrierCauchyFamily :=
  { schedule := fun f =>
      zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f
    degree := degree
    carrierData := carrierData
    separated := separated
    phiControl := phiControl }

theorem SuppliedScheduleCarrierCauchyFamily.ofCanonicalSchedule_schedule_eq
    (degree : ZetaAdmissibleFunction → ℕ)
    (carrierData :
      ∀ f : ZetaAdmissibleFunction,
        SuppliedScheduleCarrierCauchyData
          f
          (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
          (degree f))
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (phiControl :
      ∀ f : ZetaAdmissibleFunction,
        ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (f : ZetaAdmissibleFunction) :
    (SuppliedScheduleCarrierCauchyFamily.ofCanonicalSchedule
      degree carrierData separated phiControl).schedule f =
      zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f :=
  rfl

/-- Family-level direct logarithmic-derivative carrier package. -/
structure SuppliedScheduleCarrierLogDerivFamily where
  schedule :
    ∀ f : ZetaAdmissibleFunction,
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
  degree : ZetaAdmissibleFunction → ℕ
  carrierData :
    ∀ f : ZetaAdmissibleFunction,
      SuppliedScheduleCarrierLogDerivData (f) (schedule f) (degree f)
  separated :
    ∀ f : ZetaAdmissibleFunction,
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f (schedule f)).HasPositiveSingularSeparation
  phiControl :
    ∀ f : ZetaAdmissibleFunction,
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f)

def SuppliedScheduleCarrierCauchyFamily.toLogDerivFamily
    (data : SuppliedScheduleCarrierCauchyFamily) :
    SuppliedScheduleCarrierLogDerivFamily :=
  { schedule := data.schedule
    degree := data.degree
    carrierData := fun f => (data.carrierData f).toLogDerivData
    separated := data.separated
    phiControl := data.phiControl }

def SuppliedScheduleCarrierLogDerivFamily.factorBoundData
    (data : SuppliedScheduleCarrierLogDerivFamily) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaZeroExcisedStrip.FactorBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f (data.schedule f)) :=
  fun f =>
    (data.carrierData f).factorBoundData
      (data.separated f)

def SuppliedScheduleCarrierCauchyFamily.factorBoundData
    (data : SuppliedScheduleCarrierCauchyFamily) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaZeroExcisedStrip.FactorBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f (data.schedule f)) :=
  (data.toLogDerivFamily).factorBoundData

/-- A direct logarithmic-derivative carrier family gives scheduled analytic
packages for every autocorrelation seed. -/
def SuppliedScheduleCarrierLogDerivFamily.scheduledAnalyticPackage
    (data : SuppliedScheduleCarrierLogDerivFamily) :
    ∀ f : ZetaAdmissibleFunction,
      ExplicitFormulaScheduledFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  fun f =>
    (data.carrierData f).scheduledAnalyticPackage
      (data.phiControl f)
      (data.separated f)

/-- A direct logarithmic-derivative carrier family gives scheduled polynomial
packages for every autocorrelation seed. -/
def SuppliedScheduleCarrierLogDerivFamily.scheduledPolynomialPackage
    (data : SuppliedScheduleCarrierLogDerivFamily) :
    ∀ f : ZetaAdmissibleFunction,
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  fun f =>
    (data.carrierData f).scheduledPolynomialPackage
      (data.phiControl f)
      (data.separated f)

/-- A quantitative carrier family gives the scheduled analytic package family. -/
def SuppliedScheduleCarrierCauchyFamily.scheduledAnalyticPackage
    (data : SuppliedScheduleCarrierCauchyFamily) :
    ∀ f : ZetaAdmissibleFunction,
      ExplicitFormulaScheduledFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  (data.toLogDerivFamily).scheduledAnalyticPackage

/-- A quantitative carrier family gives the scheduled polynomial package
family. -/
def SuppliedScheduleCarrierCauchyFamily.scheduledPolynomialPackage
    (data : SuppliedScheduleCarrierCauchyFamily) :
    ∀ f : ZetaAdmissibleFunction,
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  (data.toLogDerivFamily).scheduledPolynomialPackage

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
