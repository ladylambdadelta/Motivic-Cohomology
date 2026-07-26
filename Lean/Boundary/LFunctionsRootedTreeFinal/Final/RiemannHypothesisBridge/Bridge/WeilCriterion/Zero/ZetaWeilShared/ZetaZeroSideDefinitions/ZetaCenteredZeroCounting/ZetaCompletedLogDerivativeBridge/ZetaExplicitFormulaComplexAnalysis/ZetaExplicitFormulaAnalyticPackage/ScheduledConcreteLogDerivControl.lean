import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledLogDerivControl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData

/-!
# Scheduled concrete completed-log-derivative control

This file constructs the scheduled horizontal log-derivative package from the
two concrete factor estimates on the actual scheduled carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Scheduled horizontal log-derivative controls over the same schedule are preserved
by union of their carriers. -/
def ExplicitFormulaScheduledHorizontalLogDerivControl.union
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (h₁ h₂ :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule) :
    ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule :=
  { carrier := CompletedZetaZeroExcisedStrip.union h₁.carrier h₂.carrier
    top_mem :=
      fun u x hx =>
        CompletedZetaZeroExcisedStrip.mem_union_left h₁.carrier h₂.carrier
          (h₁.top_mem u x hx)
    bottom_mem :=
      fun u x hx =>
        CompletedZetaZeroExcisedStrip.mem_union_left h₁.carrier h₂.carrier
          (h₁.bottom_mem u x hx)
    bound_constant :=
      fun N : ℕ => h₁.bound_constant N + h₂.bound_constant N
    bound_constant_pos :=
      fun N : ℕ =>
        add_pos (h₁.bound_constant_pos N) (h₂.bound_constant_pos N)
    bound :=
      fun N z hz =>
        let q : ℝ := (1 + ‖z.im‖) ^ N
        let qNonneg : 0 ≤ q :=
          pow_nonneg (add_nonneg zero_le_one (norm_nonneg z.im)) N
        match (Set.mem_union z h₁.carrier.carrier h₂.carrier.carrier).mp hz with
        | Or.inl hz₁ =>
            (h₁.bound N z hz₁).trans
              (mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right (le_of_lt (h₂.bound_constant_pos N)))
                qNonneg)
        | Or.inr hz₂ =>
            (h₂.bound N z hz₂).trans
              (mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_left (le_of_lt (h₁.bound_constant_pos N)))
                qNonneg) }

/-- Concrete zeta-side and inverse-Gamma bounds on the scheduled carrier construct
the narrow scheduled horizontal log-derivative control package. -/
def ExplicitFormulaScheduledHorizontalLogDerivControl.ofConcreteZetaSideAndGammaBoundData
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData carrier)
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData carrier) :
    ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule :=
  { carrier := carrier
    top_mem := topMem
    bottom_mem := bottomMem
    bound_constant :=
      fun N : ℕ => zetaData.constant N + gammaData.constant N
    bound_constant_pos :=
      fun N : ℕ =>
        add_pos (zetaData.constant_pos N) (gammaData.constant_pos N)
    bound :=
      fun N z hz =>
        completedZetaNegLogDeriv_bound_of_separated_factorBoundData
          carrier zetaData gammaData N z hz }

/- Direct owner constructor for the analytic package.  This keeps the
logarithmic-derivative estimates as the primitive input and does not require
the legacy Cauchy-factor record or a separately supplied global separation
proof. -/
def ExplicitFormulaScheduledHorizontalLogDerivControl.ofDirectLogDerivativeBounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (zetaConstant gammaConstant : ℕ → ℝ)
    (zetaConstant_pos : ∀ N : ℕ, 0 < zetaConstant N)
    (gammaConstant_pos : ∀ N : ℕ, 0 < gammaConstant N)
    (zetaBound :
      ∀ N : ℕ, ∀ z : ℂ, z ∈ carrier.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          zetaConstant N * (1 + ‖z.im‖) ^ N)
    (gammaBound :
      ∀ N : ℕ, ∀ z : ℂ, z ∈ carrier.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          gammaConstant N * (1 + ‖z.im‖) ^ N) :
    ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule :=
  { carrier := carrier
    top_mem := topMem
    bottom_mem := bottomMem
    bound_constant := fun N => zetaConstant N + gammaConstant N
    bound_constant_pos := fun N =>
      add_pos (zetaConstant_pos N) (gammaConstant_pos N)
    bound := fun N z hz =>
      completedZetaNegLogDeriv_bound_of_concrete_zetaSide_and_gamma
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier N
        (zetaConstant N) (gammaConstant N)
        (zetaBound N) (gammaBound N) z hz }

def ExplicitFormulaScheduledHorizontalLogDerivControl.ofFactorBoundData
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (factorData :
      CompletedZetaZeroExcisedStrip.FactorBoundData carrier) :
    ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule :=
  ExplicitFormulaScheduledHorizontalLogDerivControl.ofConcreteZetaSideAndGammaBoundData
    carrier topMem bottomMem factorData.zetaSide factorData.inverseGamma

def ExplicitFormulaScheduledHorizontalLogDerivControl.ofFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈
            boundedCarrier.carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈
            boundedCarrier.carrier.carrier) :
    ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule :=
  ExplicitFormulaScheduledHorizontalLogDerivControl.ofFactorBoundData
    boundedCarrier.carrier topMem bottomMem boundedCarrier.factorBound

/- The zero-degree specialization is the concrete finite-height estimate used
   when the contour argument has already fixed its scheduled height. -/
theorem ExplicitFormulaScheduledHorizontalLogDerivControl.bound_zero_owner
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (control : ExplicitFormulaScheduledHorizontalLogDerivControl
      f F heightSchedule)
    {z : ℂ} (hz : z ∈ control.carrier.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤ control.bound_constant 0 := by
  have hbound := control.bound 0 z hz
  have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
  exact hbound.trans_eq
    (Eq.trans
      (congrArg (fun q : ℝ => control.bound_constant 0 * q) hpow)
      (mul_one (control.bound_constant 0)))

/-- Concrete factor bounds on the scheduled horizontal carrier construct the
scheduled analytic package. -/
def ExplicitFormulaScheduledFamilyAnalyticPackage.ofConcreteZetaSideAndGammaBoundData
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (phiControl : ZetaPhiAnalyticControl f)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F)
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData carrier)
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData carrier) :
    ExplicitFormulaScheduledFamilyAnalyticPackage f F :=
  { phi_control := phiControl
    height_schedule := heightSchedule
    horizontal_logderiv_control :=
      ExplicitFormulaScheduledHorizontalLogDerivControl.ofConcreteZetaSideAndGammaBoundData
        carrier topMem bottomMem zetaData gammaData }

/- The family-level direct constructor is the consumer-facing form of the
owner theorem above. -/
def ExplicitFormulaScheduledFamilyAnalyticPackage.ofDirectLogDerivativeBounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (phiControl : ZetaPhiAnalyticControl f)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F)
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (zetaConstant gammaConstant : ℕ → ℝ)
    (zetaConstant_pos : ∀ N : ℕ, 0 < zetaConstant N)
    (gammaConstant_pos : ∀ N : ℕ, 0 < gammaConstant N)
    (zetaBound :
      ∀ N : ℕ, ∀ z : ℂ, z ∈ carrier.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          zetaConstant N * (1 + ‖z.im‖) ^ N)
    (gammaBound :
      ∀ N : ℕ, ∀ z : ℂ, z ∈ carrier.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          gammaConstant N * (1 + ‖z.im‖) ^ N) :
    ExplicitFormulaScheduledFamilyAnalyticPackage f F :=
  { phi_control := phiControl
    height_schedule := heightSchedule
    horizontal_logderiv_control :=
      ExplicitFormulaScheduledHorizontalLogDerivControl.ofDirectLogDerivativeBounds
        carrier topMem bottomMem zetaConstant gammaConstant
        zetaConstant_pos gammaConstant_pos zetaBound gammaBound }

def ExplicitFormulaScheduledFamilyAnalyticPackage.ofFactorBoundData
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (phiControl : ZetaPhiAnalyticControl f)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F)
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (factorData :
      CompletedZetaZeroExcisedStrip.FactorBoundData carrier) :
    ExplicitFormulaScheduledFamilyAnalyticPackage f F :=
  ExplicitFormulaScheduledFamilyAnalyticPackage.ofConcreteZetaSideAndGammaBoundData
    phiControl heightSchedule carrier topMem bottomMem
    factorData.zetaSide factorData.inverseGamma

def ExplicitFormulaScheduledFamilyAnalyticPackage.ofFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (phiControl : ZetaPhiAnalyticControl f)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F)
    (boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈
            boundedCarrier.carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈
            boundedCarrier.carrier.carrier) :
    ExplicitFormulaScheduledFamilyAnalyticPackage f F :=
  ExplicitFormulaScheduledFamilyAnalyticPackage.ofFactorBoundData
    phiControl heightSchedule boundedCarrier.carrier topMem bottomMem
    boundedCarrier.factorBound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
