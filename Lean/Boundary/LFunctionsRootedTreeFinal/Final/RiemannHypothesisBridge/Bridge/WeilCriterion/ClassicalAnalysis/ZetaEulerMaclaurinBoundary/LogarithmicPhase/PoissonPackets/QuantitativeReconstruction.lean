import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeSupport

/-!
# Exact Poisson reconstruction for the quantitative logarithmic cutoff

This is the discrete identity for the fixed-collar test function.  Its sample
proof is separated from the analytic estimates: the cutoff equals one exactly
on the selected integer block and zero at every other integer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.logarithmicPhaseQuantitativeBlockSchwartz_eval_of_mem
    (t : ℝ)
    (a b n : ℤ)
    (ha : 1 ≤ a)
    (hn : n ∈ Finset.Icc a b) :
    Complex.logarithmicPhaseQuantitativeBlockSchwartz t a b ha (n : ℝ) =
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t (n : ℝ) : ℂ)) := by
  exact
    (congrArg
      (fun value : ℝ =>
        value •
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ)))
      (Real.quantitativeLogarithmicBlockCutoff_eq_one_of_mem_Icc_int hn)).trans
      (one_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))))

theorem Complex.logarithmicPhaseQuantitativeBlockSchwartz_eval_eq_zero_of_not_mem
    (t : ℝ)
    (a b n : ℤ)
    (ha : 1 ≤ a)
    (hn : n ∉ Finset.Icc a b) :
    Complex.logarithmicPhaseQuantitativeBlockSchwartz t a b ha (n : ℝ) = 0 := by
  exact
    (congrArg
      (fun value : ℝ =>
        value •
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ)))
      (Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_not_mem_Icc hn)).trans
      (zero_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))))

def Complex.logarithmicPhaseQuantitativeBlockFourierPacket
    (t : ℝ)
    (a b m : ℤ) : ℂ :=
  ∫ x : ℝ,
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b) m x

theorem Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_transform
    (t : ℝ)
    (a b m : ℤ)
    (ha : 1 ≤ a) :
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
      SchwartzMap.fourierTransformCLM ℝ
        (Complex.logarithmicPhaseQuantitativeBlockSchwartz t a b ha)
        (m : ℝ) := by
  exact
    (Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_frequencyTwistIntegral
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b)
      (Complex.contDiff_logarithmicPhase_quantitativeBlockCutoffFunction t a b ha)
      (Real.hasCompactSupport_quantitativeLogarithmicBlockCutoff a b)
      m).symm

theorem Complex.logarithmicPhase_quantitativeBlock_poisson_packet_reconstruction
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))) =
      ∑' m : ℤ, Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m := by
  let extension : SchwartzMap ℝ ℂ :=
    Complex.logarithmicPhaseQuantitativeBlockSchwartz t a b ha
  have hreconstruction :=
    Complex.finite_integerSample_poisson_reconstruction
      extension
      (Finset.Icc a b)
      (fun n hn =>
        Complex.logarithmicPhaseQuantitativeBlockSchwartz_eval_eq_zero_of_not_mem
          t a b n ha hn)
  have hsamples :
      (∑ n ∈ Finset.Icc a b, extension (n : ℝ)) =
        ∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ)) :=
    Finset.sum_congr rfl
      (fun n hn =>
        Complex.logarithmicPhaseQuantitativeBlockSchwartz_eval_of_mem
          t a b n ha hn)
  have hmode :
      ∀ m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ) =
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m :=
    fun m : ℤ =>
      (Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_transform
        t a b m ha).symm
  exact hsamples.symm.trans (hreconstruction.trans (tsum_congr hmode))

theorem Complex.summable_logarithmicPhaseQuantitativeBlockFourierPacket
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    Summable (fun m : ℤ =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  let extension : SchwartzMap ℝ ℂ :=
    Complex.logarithmicPhaseQuantitativeBlockSchwartz t a b ha
  have hsum :
      Summable (fun m : ℤ =>
        SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ)) :=
    Complex.summable_logarithmicPhase_integerBlockFourierPacket extension
  have hmode :
      ∀ m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ) =
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m :=
    fun m : ℤ =>
      (Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_transform
        t a b m ha).symm
  exact hsum.congr hmode

end
end LFunctions
end Boundary
