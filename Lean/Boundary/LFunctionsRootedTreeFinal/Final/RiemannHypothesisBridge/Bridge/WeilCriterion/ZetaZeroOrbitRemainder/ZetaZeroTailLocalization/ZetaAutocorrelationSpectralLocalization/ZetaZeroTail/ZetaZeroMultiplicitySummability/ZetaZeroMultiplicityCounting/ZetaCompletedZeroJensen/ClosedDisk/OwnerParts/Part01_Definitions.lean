import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaPolynomialTailSummability.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaCenteredZeroVerticalStrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroLocalFiniteness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.ZeroCarrier.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

namespace Boundary
namespace LFunctions

noncomputable section

/-- Multiplicity summand for completed zeros inside a centered closed disk. -/
noncomputable def completedZeroMultiplicityClosedDiskSummand
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  if ‖(ρ : ℂ)‖ ≤ R then
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  else
    0

/-- Completed-zero multiplicity count in the centered closed disk of radius `R`. -/
noncomputable def completedZeroMultiplicityCountingInCenteredClosedDisk
    (R : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    completedZeroMultiplicityClosedDiskSummand R ρ

/-- Completed zeros in the centered ordinary closed disk of radius `R`. -/
def completedZerosInCenteredClosedDisk
    (R : ℝ) : Set {ρ : ℂ // ZetaCompletedZero ρ} :=
  {ρ | ‖(ρ : ℂ)‖ ≤ R}

/-- Zeros of the centered entire zero-carrier. -/
abbrev CenteredCompletedZetaZeroCarrierZero : Type :=
  {z : ℂ // centeredCompletedRiemannZetaZeroCarrier z = 0}

/-- Multiplicity of a zero of the centered entire zero-carrier. -/
noncomputable def centeredCompletedZetaZeroCarrierMultiplicity
    (z : ℂ) : ℕ :=
  (centeredCompletedRiemannZetaZeroCarrier_analyticAt z).order.toNat

/-- Multiplicity summand for carrier zeros inside a centered closed disk. -/
noncomputable def centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero) : ℝ :=
  if ‖(z : ℂ)‖ ≤ R then
    (centeredCompletedZetaZeroCarrierMultiplicity (z : ℂ) : ℝ)
  else
    0

/-- Carrier-zero multiplicity count in the centered closed disk of radius `R`. -/
noncomputable def centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk
    (R : ℝ) : ℝ :=
  ∑' z : CenteredCompletedZetaZeroCarrierZero,
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z

/-- The carrier summand is the generic entire-function summand. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_eq_entire
    (R : ℝ)
    (z : CenteredCompletedZetaZeroCarrierZero) :
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z =
      entireFunctionZeroMultiplicityClosedDiskSummand
        centeredCompletedRiemannZetaZeroCarrier
        centeredCompletedRiemannZetaZeroCarrier_analyticAt
        R
        z := by
  exact Eq.refl
    (centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)

/-- The carrier count is the generic entire-function count. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk_eq_entire
    (R : ℝ) :
    centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R =
      entireFunctionZeroMultiplicityCountingInClosedDisk
        centeredCompletedRiemannZetaZeroCarrier
        centeredCompletedRiemannZetaZeroCarrier_analyticAt
        R := by
  exact Eq.refl
    (centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R)

/-- Carrier zeros in the centered ordinary closed disk of radius `R`. -/
def centeredCompletedZetaZeroCarrierZerosInClosedDisk
    (R : ℝ) : Set CenteredCompletedZetaZeroCarrierZero :=
  {z | ‖(z : ℂ)‖ ≤ R}

end

end LFunctions
end Boundary
