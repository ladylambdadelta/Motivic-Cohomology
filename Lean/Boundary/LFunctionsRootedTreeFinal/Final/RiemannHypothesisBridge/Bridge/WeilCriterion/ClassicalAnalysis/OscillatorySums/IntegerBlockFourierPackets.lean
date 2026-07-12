import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.PhaseCutoffFourierMode

/-!
# Fourier packets for finite integer blocks

This file is the owner bridge from exact finite Poisson reconstruction to the
continuous packets estimated by stationary and nonstationary phase.  Each
packet uses the canonical integer-block cutoff and the correctly normalized
frequency twist `φ(x) - 2πmx`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped ContDiff

/-- The canonical continuous Fourier packet attached to mode `m` and the
ordered integer block `[a,b]`. -/
def Complex.integerBlockFourierPacket
    (phase : ℝ → ℝ)
    (a b : ℤ)
    (m : ℤ) : ℂ :=
  ∫ x : ℝ,
    Complex.phaseCutoffFrequencyTwistIntegrand
      phase (Real.integerBlockCutoff a b) m x

/-- A Fourier coefficient of the canonical integer-block Schwartz extension
is exactly its continuous frequency packet. -/
theorem Complex.fourierTransform_integerBlockPhaseCutoff_eq_packet
    (phase : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (a b m : ℤ) :
    SchwartzMap.fourierTransformCLM ℝ
        (Complex.phaseCutoffSchwartz
          phase
          (Real.integerBlockCutoff a b)
          hphase
          (Real.contDiff_integerBlockCutoff a b)
          (Real.hasCompactSupport_integerBlockCutoff a b))
        (m : ℝ) =
      Complex.integerBlockFourierPacket phase a b m := by
  exact
    Complex.fourierTransform_phaseCutoffSchwartz_eq_frequencyTwistIntegral
      phase
      (Real.integerBlockCutoff a b)
      hphase
      (Real.contDiff_integerBlockCutoff a b)
      (Real.hasCompactSupport_integerBlockCutoff a b)
      m

/-- Exact packet reconstruction of an ordered finite integer exponential
sum.  This is the analytic input boundary for all later packet estimates. -/
theorem Complex.integerBlock_poisson_packet_reconstruction
    (phase : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (a b : ℤ)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (phase (n : ℝ) : ℂ))) =
      ∑' m : ℤ,
        Complex.integerBlockFourierPacket phase a b m := by
  have hreconstruction :=
    Complex.integerBlock_poisson_reconstruction phase hphase a b hab
  have hcoefficient :
      ∀ m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ
            (Complex.phaseCutoffSchwartz
              phase
              (Real.integerBlockCutoff a b)
              hphase
              (Real.contDiff_integerBlockCutoff a b)
              (Real.hasCompactSupport_integerBlockCutoff a b))
            (m : ℝ) =
          Complex.integerBlockFourierPacket phase a b m :=
    fun m : ℤ =>
      Complex.fourierTransform_integerBlockPhaseCutoff_eq_packet
        phase hphase a b m
  have hseries :
      (∑' m : ℤ,
          SchwartzMap.fourierTransformCLM ℝ
            (Complex.phaseCutoffSchwartz
              phase
              (Real.integerBlockCutoff a b)
              hphase
              (Real.contDiff_integerBlockCutoff a b)
              (Real.hasCompactSupport_integerBlockCutoff a b))
            (m : ℝ)) =
        ∑' m : ℤ,
          Complex.integerBlockFourierPacket phase a b m :=
    tsum_congr hcoefficient
  exact hreconstruction.trans hseries

end

end LFunctions
end Boundary
