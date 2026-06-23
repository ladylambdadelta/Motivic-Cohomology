import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaPolynomialTailSummability.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaCenteredZeroVerticalStrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroLocalFiniteness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.ZeroCarrier.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

/-!
# Closed-disk completed-zero counting

This owner layer contains closed-disk zero counting definitions, finiteness, and summability.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

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

/-- The carrier closed-disk summand is the generic entire-function closed-disk summand
for the centered completed-zeta zero carrier. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_eq_entire
    (R : ℝ)
    (z : CenteredCompletedZetaZeroCarrierZero) :
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z =
      entireFunctionZeroMultiplicityClosedDiskSummand
        centeredCompletedRiemannZetaZeroCarrier
        centeredCompletedRiemannZetaZeroCarrier_analyticAt
        R
        z := by
  rfl

/-- The carrier closed-disk count is the generic entire-function closed-disk count
for the centered completed-zeta zero carrier. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk_eq_entire
    (R : ℝ) :
    centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R =
      entireFunctionZeroMultiplicityCountingInClosedDisk
        centeredCompletedRiemannZetaZeroCarrier
        centeredCompletedRiemannZetaZeroCarrier_analyticAt
        R := by
  rfl

/-- Carrier zeros in the centered ordinary closed disk of radius `R`. -/
def centeredCompletedZetaZeroCarrierZerosInClosedDisk
    (R : ℝ) : Set CenteredCompletedZetaZeroCarrierZero :=
  {z | ‖(z : ℂ)‖ ≤ R}

/-- Closed-disk multiplicity summands are nonnegative. -/
theorem completedZeroMultiplicityClosedDiskSummand_nonnegative
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    [Decidable (‖(ρ : ℂ)‖ ≤ R)] :
    0 ≤ completedZeroMultiplicityClosedDiskSummand R ρ := by
  exact
    match (inferInstance : Decidable (‖(ρ : ℂ)‖ ≤ R)) with
    | Or.inl hρ =>
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_pos hρ).symm
          (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))
    | Or.inr hρ =>
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_neg hρ).symm
          (le_refl (0 : ℝ))

/-- Closed-disk multiplicity summands vanish outside the closed disk. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_zero_of_not_mem
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∉ completedZerosInCenteredClosedDisk R) :
    completedZeroMultiplicityClosedDiskSummand R ρ = 0 := by
  exact if_neg hρ

/-- Centering by the real half-shift preserves the imaginary coordinate. -/
theorem zetaCenteredZero_im_eq
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaCenteredZero (ρ : ℂ)).im = (ρ : ℂ).im := by
  calc
    ((ρ : ℂ) - (1 / 2 : ℂ)).im =
        (ρ : ℂ).im - (1 / 2 : ℂ).im := by
      exact Complex.sub_im (ρ : ℂ) (1 / 2 : ℂ)
    _ = (ρ : ℂ).im - (0 : ℝ) := by
      have hhalf_im : (1 / 2 : ℂ).im = 0 := by
        calc
          (1 / 2 : ℂ).im = ((1 : ℂ) / (2 : ℝ)).im := by
            rfl
          _ = (1 : ℂ).im / (2 : ℝ) := by
            exact Complex.div_ofReal_im (1 : ℂ) 2
          _ = (0 : ℝ) / (2 : ℝ) := by
            exact congrArg (fun x : ℝ => x / (2 : ℝ)) Complex.one_im
          _ = 0 := by
            exact zero_div 2
      exact congrArg (fun x : ℝ => (ρ : ℂ).im - x)
        hhalf_im
    _ = (ρ : ℂ).im := by
      exact sub_zero (ρ : ℂ).im

/-- A completed zero in an ordinary closed disk lies in the enlarged centered-height ball. -/
theorem completedZero_mem_centeredHeightBall_of_mem_centeredClosedDisk
    (R : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ completedZerosInCenteredClosedDisk R) :
    ρ ∈ completedZerosInCenteredHeightBall (R + 1) := by
  have him :
      ‖(zetaCenteredZero (ρ : ℂ)).im‖ = ‖(ρ : ℂ).im‖ :=
    congrArg (fun x : ℝ => ‖x‖) (zetaCenteredZero_im_eq ρ)
  have him_norm :
      ‖(ρ : ℂ).im‖ ≤ ‖(ρ : ℂ)‖ :=
    Complex.abs_im_le_abs (ρ : ℂ)
  have him_centered_norm :
      ‖(zetaCenteredZero (ρ : ℂ)).im‖ ≤ ‖(ρ : ℂ)‖ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖(ρ : ℂ)‖)
      him.symm
      him_norm
  have hheight_le_one_add_norm :
      1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖ ≤ 1 + ‖(ρ : ℂ)‖ :=
    add_le_add_left him_centered_norm 1
  have hone_add_norm_le_one_add_R :
      1 + ‖(ρ : ℂ)‖ ≤ 1 + R :=
    add_le_add_left hρ 1
  have hone_add_R_eq_R_add_one : 1 + R = R + 1 :=
    add_comm 1 R
  exact le_trans hheight_le_one_add_norm
    (Eq.subst
      (motive := fun x : ℝ => 1 + ‖(ρ : ℂ)‖ ≤ x)
      hone_add_R_eq_R_add_one
      hone_add_norm_le_one_add_R)

/-- Centered ordinary closed disks contain only finitely many completed zeros. -/
theorem finite_completedZerosInCenteredClosedDisk
    (R : ℝ) :
    (completedZerosInCenteredClosedDisk R).Finite := by
  exact Set.Finite.subset
    (finite_completedZerosInCenteredHeightBall (R + 1))
    (fun ρ hρ =>
      completedZero_mem_centeredHeightBall_of_mem_centeredClosedDisk R ρ hρ)

/-- Finite closed disks make the closed-disk multiplicity summand summable. -/
theorem summable_completedZeroMultiplicityClosedDiskSummand_of_finite_closedDisk
    (R : ℝ)
    (hfinite : (completedZerosInCenteredClosedDisk R).Finite) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityClosedDiskSummand R ρ) := by
  exact summable_of_finite_support_real
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityClosedDiskSummand R ρ)
    (completedZerosInCenteredClosedDisk R)
    hfinite
    (completedZeroMultiplicityClosedDiskSummand_eq_zero_of_not_mem R)

/-- Closed-disk multiplicity summands are summable. -/
theorem summable_completedZeroMultiplicityClosedDiskSummand
    (R : ℝ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityClosedDiskSummand R ρ) := by
  exact summable_completedZeroMultiplicityClosedDiskSummand_of_finite_closedDisk
    R
    (finite_completedZerosInCenteredClosedDisk R)

end

end LFunctions
end Boundary
