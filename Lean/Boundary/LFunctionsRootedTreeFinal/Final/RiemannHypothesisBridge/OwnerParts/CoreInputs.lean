import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.CoherenceComponents
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.Prelude
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.OffCriticalSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointReservePositivity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.ForcedDaggerTailParts.Reconstruction

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

theorem boundaryRiemannHypothesis_eq_mathlib :
    boundaryRiemannHypothesis = RiemannHypothesis :=
  Eq.refl boundaryRiemannHypothesis

theorem boundaryCompletedRiemannZeta_eq_mathlib :
    boundaryCompletedRiemannZeta = completedRiemannZeta :=
  Eq.refl boundaryCompletedRiemannZeta

theorem boundaryRiemannZeta_eq_mathlib :
    boundaryRiemannZeta = riemannZeta :=
  Eq.refl boundaryRiemannZeta

theorem finalRiemannHypothesis_separatedZeroTailSmallValuesOwnerRunge
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      (∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
            r < ε :=
  ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberDirectCenteredZeroTailSmallValuesRunge_owner
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary

theorem finalRiemannHypothesis_binetEndpointRestoredFiniteHeightContourInputs :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs :=
  Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

theorem finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  poleClearedRightCriticalStripAdmissibleGrowth_owner hbranch hreflected

def FinalEndpointTraceReserveDomination : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ZetaAdmissibleFunction.ZetaCompletedEndpointTraceReserveDomination f

theorem finalRiemannHypothesis_endpointTraceReserveDomination_owner :
    FinalEndpointTraceReserveDomination :=
  fun f =>
    ZetaAdmissibleFunction.zetaCompletedEndpointTraceReserveDomination_owner f

theorem finalRiemannHypothesis_endpointDiagonalDebtScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ ZetaAdmissibleFunction.zetaCompletedEndpointDiagonalDebtScalar f :=
  (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt_nonnegative

theorem finalRiemannHypothesis_right_le_add_of_left_nonnegative
    (left right : ℝ) (hleft : 0 ≤ left) :
    right ≤ left + right :=
  Eq.subst
    (motive := fun value : ℝ => value ≤ left + right)
    (zero_add right)
    (add_le_add_right hleft right)

def FinalPhysicalArchimedeanAbsorption : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
      ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
        ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
        ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f

theorem finalPhysicalArchimedeanAbsorption_of_endpointTraceReserveDomination
    (reserveDomination : FinalEndpointTraceReserveDomination) :
    FinalPhysicalArchimedeanAbsorption :=
  fun f =>
    let hdebtNonnegative :
        0 ≤ ZetaAdmissibleFunction.zetaCompletedEndpointDiagonalDebtScalar f :=
      finalRiemannHypothesis_endpointDiagonalDebtScalar_nonnegative f
    let hnegative_le_combined :
        ZetaAdmissibleFunction.zetaCompletedNegativeArchimedeanDebtScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedEndpointDiagonalDebtScalar f +
            ZetaAdmissibleFunction.zetaCompletedNegativeArchimedeanDebtScalar f :=
      finalRiemannHypothesis_right_le_add_of_left_nonnegative
        (ZetaAdmissibleFunction.zetaCompletedEndpointDiagonalDebtScalar f)
        (ZetaAdmissibleFunction.zetaCompletedNegativeArchimedeanDebtScalar f)
        hdebtNonnegative
    let hcombined :
        ZetaAdmissibleFunction.zetaCompletedEndpointDiagonalDebtScalar f +
            ZetaAdmissibleFunction.zetaCompletedNegativeArchimedeanDebtScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedNormalizedSignedReserveScalar f :=
      reserveDomination f
    let habsorption :
        ZetaAdmissibleFunction.zetaCompletedNegativeArchimedeanDebtScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedNormalizedSignedReserveScalar f :=
      le_trans hnegative_le_combined hcombined
    show
      ZetaAdmissibleFunction.zetaCompletedNegativeArchimedeanDebtScalar f ≤
        ZetaAdmissibleFunction.zetaCompletedNormalizedSignedReserveScalar f
      from habsorption

end
end LFunctions
end Boundary
