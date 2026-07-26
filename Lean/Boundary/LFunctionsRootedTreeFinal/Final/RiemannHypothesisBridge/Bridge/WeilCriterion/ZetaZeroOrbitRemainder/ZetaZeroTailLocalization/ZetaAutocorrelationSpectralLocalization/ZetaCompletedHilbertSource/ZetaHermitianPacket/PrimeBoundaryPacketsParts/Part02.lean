import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeBoundaryPacketsParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The positive prime defect kernel over the explicit prime support. -/
noncomputable def zetaPrimeDefectKernelPositiveForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f

/-- The displayed finite-support positive prime defect-kernel form vanishes under the current
completed lower-weight normalization. -/
theorem zetaPrimeDefectKernelPositiveForm_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelPositiveForm f = 0 := by
  unfold zetaPrimeDefectKernelPositiveForm
  exact Finset.sum_eq_zero
    (fun ℓ hℓ => by
      have hpos :
          zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f = 0 :=
        zetaCompletedExplicitFormulaPrimeSpectralAmplitude_eq_zero_of_mem_support
          f hℓ
      have hneg :
          zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f = 0 :=
        zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude_eq_zero_of_mem_support
          f hℓ
      unfold zetaPrimeDefectKernelPositiveCoordinate
      calc
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f -
              zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) *
            star
              (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f -
                zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) =
            (0 - 0) * star (0 - 0 : ℂ) := by
          exact congrArg₂ HMul.hMul
            (congrArg₂ Sub.sub hpos hneg)
            (congrArg star (congrArg₂ Sub.sub hpos hneg))
        _ = 0 * star (0 - 0 : ℂ) := by
          exact congrArg
            (fun z : ℂ => z * star (0 - 0 : ℂ))
            (sub_self (0 : ℂ))
        _ = 0 := by
          exact zero_mul (star (0 - 0 : ℂ)))

/-- Real form of the completed lower-weight normalization for the displayed finite-support
positive prime defect-kernel form. -/
theorem zetaPrimeDefectKernelPositiveForm_re_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelPositiveForm f) = 0 := by
  exact Eq.trans
    (congrArg Complex.re
      (zetaPrimeDefectKernelPositiveForm_eq_zero_of_completedLowerWeightNormalization f))
    Complex.zero_re

/-- The additive cancellation at the end of the one-coordinate defect-square expansion. -/
theorem defect_square_cross_cancel
    (x y z w : ℂ) :
    ((x - y) - (z - w)) + (z + y) = x + w :=
  calc
    ((x - y) - (z - w)) + (z + y) =
        ((x - y) + (w - z)) + (z + y) := by
      exact congrArg (fun t : ℂ => t + (z + y))
        (calc
          (x - y) - (z - w) = (x - y) + -(z - w) := by
            exact sub_eq_add_neg (x - y) (z - w)
          _ = (x - y) + (w - z) := by
            exact congrArg (fun t : ℂ => (x - y) + t) (neg_sub z w))
    _ = (x - y) + ((w - z) + (z + y)) := by
      exact add_assoc (x - y) (w - z) (z + y)
    _ = (x - y) + (w + y) := by
      exact congrArg (fun t : ℂ => (x - y) + t)
        (calc
          (w - z) + (z + y) = ((w - z) + z) + y := by
            exact (add_assoc (w - z) z y).symm
          _ = w + y := by
            exact congrArg (fun t : ℂ => t + y) (sub_add_cancel w z))
    _ = (x - y) + (y + w) := by
      exact congrArg (fun t : ℂ => (x - y) + t) (add_comm w y)
    _ = ((x - y) + y) + w := by
      exact (add_assoc (x - y) y w).symm
    _ = x + w := by
      exact congrArg (fun t : ℂ => t + w) (sub_add_cancel x y)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
