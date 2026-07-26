import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.RenormalizedTraceExhaustion

/-!
# Endpoint finite GNS capture

This file owns the finite GNS capture statement for the endpoint fiber inside
the renormalized positive trace model.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Finite GNS capture of the endpoint fiber by the positive trace model. -/
structure CompletedEndpointFiniteGNSCapture
    (N : ℕ) (f : ZetaAdmissibleFunction) where
  ambientTrace : ℝ
  endpointTrace : ℝ
  orthogonalTrace : ℝ
  ambientTrace_eq :
    ambientTrace = finitePositiveRenormalizedBoundaryWindow N f
  endpointTrace_eq :
    endpointTrace = (completedWeilEndpointTraceFiber f).gram
  orthogonalTrace_eq :
    orthogonalTrace = completedEndpointPhysicalHiddenKernelWindow N f
  trace_split :
    ambientTrace = endpointTrace + orthogonalTrace
  orthogonalTrace_nonnegative :
    0 ≤ orthogonalTrace

/-- A threshold after which every finite positive trace model captures the
endpoint fiber. -/
def CompletedEndpointFiniteGNSCaptureThreshold
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ cutoff : ℕ,
    ∀ N : ℕ,
      cutoff ≤ N →
        Nonempty (CompletedEndpointFiniteGNSCapture N f)

/-- Eventual nonnegativity of the finite hidden endpoint-kernel windows. -/
def CompletedEndpointFiniteHiddenKernelNonnegativeExhaustion
    (f : ZetaAdmissibleFunction) : Prop :=
  ∀ᶠ N in atTop,
    0 ≤ completedEndpointPhysicalHiddenKernelWindow N f

/-- Threshold form of finite hidden endpoint-kernel nonnegativity. -/
def CompletedEndpointFiniteHiddenKernelNonnegativeThreshold
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ cutoff : ℕ,
    ∀ N : ℕ,
      cutoff ≤ N →
        0 ≤ completedEndpointPhysicalHiddenKernelWindow N f

/-- Eventual finite GNS capture is the threshold form of finite GNS capture. -/
theorem completedEndpointFiniteGNSCaptureThreshold_of_eventually
    (f : ZetaAdmissibleFunction)
    (heventual :
      ∀ᶠ N in atTop,
        Nonempty (CompletedEndpointFiniteGNSCapture N f)) :
    CompletedEndpointFiniteGNSCaptureThreshold f :=
  Filter.eventually_atTop.1 heventual

/-- A concrete finite GNS capture threshold gives eventual finite GNS
capture. -/
theorem completedEndpointFiniteGNSCapture_eventually_of_threshold
    (f : ZetaAdmissibleFunction)
    (hthreshold : CompletedEndpointFiniteGNSCaptureThreshold f) :
    ∀ᶠ N in atTop,
      Nonempty (CompletedEndpointFiniteGNSCapture N f) :=
  match hthreshold with
  | ⟨cutoff, hcutoff⟩ =>
      Filter.eventually_atTop.2
        ⟨cutoff, hcutoff⟩

/-- A finite GNS capture gives nonnegativity of the finite physical
hidden-kernel window. -/
theorem completedEndpointPhysicalHiddenKernelWindow_nonnegative_of_finiteGNSCapture
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (capture : CompletedEndpointFiniteGNSCapture N f) :
    0 ≤ completedEndpointPhysicalHiddenKernelWindow N f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    capture.orthogonalTrace_eq
    capture.orthogonalTrace_nonnegative

/-- A nonnegative finite physical hidden-kernel window constructs the finite
GNS capture package. -/
def completedEndpointFiniteGNSCapture_of_hiddenKernelWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hkernel : 0 ≤ completedEndpointPhysicalHiddenKernelWindow N f) :
    CompletedEndpointFiniteGNSCapture N f :=
  { ambientTrace := finitePositiveRenormalizedBoundaryWindow N f
    endpointTrace := (completedWeilEndpointTraceFiber f).gram
    orthogonalTrace := completedEndpointPhysicalHiddenKernelWindow N f
    ambientTrace_eq :=
      Eq.refl (finitePositiveRenormalizedBoundaryWindow N f)
    endpointTrace_eq :=
      Eq.refl ((completedWeilEndpointTraceFiber f).gram)
    orthogonalTrace_eq :=
      Eq.refl (completedEndpointPhysicalHiddenKernelWindow N f)
    trace_split :=
      endpointTraceDebt_add_sub_cancel
        (finitePositiveRenormalizedBoundaryWindow N f)
        ((completedWeilEndpointTraceFiber f).gram)
    orthogonalTrace_nonnegative := hkernel }

/-- A scalar hidden-kernel nonnegativity threshold constructs a finite GNS
capture threshold. -/
theorem completedEndpointFiniteGNSCaptureThreshold_of_hiddenKernelNonnegativeThreshold
    (f : ZetaAdmissibleFunction)
    (hthreshold :
      CompletedEndpointFiniteHiddenKernelNonnegativeThreshold f) :
    CompletedEndpointFiniteGNSCaptureThreshold f :=
  match hthreshold with
  | ⟨cutoff, hcutoff⟩ =>
      Exists.intro cutoff
        fun N hcutoffLe =>
          Nonempty.intro
            (completedEndpointFiniteGNSCapture_of_hiddenKernelWindow_nonnegative
              N f (hcutoff N hcutoffLe))

/-- The finite physical hidden-kernel window is the hidden scalar of the
concrete finite positive trace matrix. -/
theorem completedEndpointPhysicalHiddenKernelWindow_eq_positiveTraceMatrix_hiddenKernelScalar
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointPhysicalHiddenKernelWindow N f =
      (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
  Eq.refl (completedEndpointPhysicalHiddenKernelWindow N f)

/-- Hidden-kernel nonnegativity constructs finite GNS capture, eventually. -/
theorem completedEndpointFiniteGNSCapture_eventually_of_hiddenKernelNonnegative
    (f : ZetaAdmissibleFunction)
    (hhidden :
      CompletedEndpointFiniteHiddenKernelNonnegativeExhaustion f) :
    ∀ᶠ N in atTop,
      Nonempty (CompletedEndpointFiniteGNSCapture N f) :=
  hhidden.mono
    (fun N hN =>
      Nonempty.intro
        (completedEndpointFiniteGNSCapture_of_hiddenKernelWindow_nonnegative
          N f hN))

/-- Positive-trace-matrix hidden-kernel nonnegativity gives physical
hidden-kernel window nonnegativity. -/
theorem completedEndpointFiniteHiddenKernelNonnegativeExhaustion_of_positiveTraceMatrix
    (f : ZetaAdmissibleFunction)
    (hmatrix :
      ∀ᶠ N in atTop,
        0 ≤
          (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar) :
    CompletedEndpointFiniteHiddenKernelNonnegativeExhaustion f :=
  hmatrix.mono
    (fun N hN =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedEndpointPhysicalHiddenKernelWindow_eq_positiveTraceMatrix_hiddenKernelScalar
          N f).symm
        hN)

/-- Source scalar threshold for finite hidden endpoint-kernel nonnegativity. -/
theorem completedEndpointFiniteHiddenKernelNonnegativeThreshold_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    CompletedEndpointFiniteHiddenKernelNonnegativeThreshold f :=
  Filter.eventually_atTop.1
    (completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_traceExhaustion_source
      f D hnonPrime)

/-- Source finite GNS endpoint capture threshold. -/
theorem completedEndpointFiniteGNSCaptureThreshold_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    CompletedEndpointFiniteGNSCaptureThreshold f :=
  completedEndpointFiniteGNSCaptureThreshold_of_hiddenKernelNonnegativeThreshold
    f
    (completedEndpointFiniteHiddenKernelNonnegativeThreshold_source
      f D hnonPrime)

/-- Source finite GNS endpoint capture. -/
theorem completedEndpointFiniteGNSCapture_eventually_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      Nonempty (CompletedEndpointFiniteGNSCapture N f) :=
  completedEndpointFiniteGNSCapture_eventually_of_threshold
    f
    (completedEndpointFiniteGNSCaptureThreshold_source f D hnonPrime)

/-- Source finite physical hidden-kernel window nonnegativity from finite GNS
capture. -/
theorem completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_of_finiteGNSCapture_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      0 ≤ completedEndpointPhysicalHiddenKernelWindow N f :=
  (completedEndpointFiniteGNSCapture_eventually_source f D hnonPrime).mono
    (fun N hN =>
      match hN with
      | ⟨capture⟩ =>
          completedEndpointPhysicalHiddenKernelWindow_nonnegative_of_finiteGNSCapture
            N f capture)

/-- Source eventual finite hidden-kernel nonnegativity. -/
theorem completedEndpointFiniteHiddenKernelNonnegativeExhaustion_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    CompletedEndpointFiniteHiddenKernelNonnegativeExhaustion f :=
  completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_of_finiteGNSCapture_source
    f D hnonPrime

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
