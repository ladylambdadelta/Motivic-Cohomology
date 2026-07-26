import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.TraceEnergyPrimitive
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingSpectralOwner
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime positive trace-energy source

This file owns the packet-level trace-energy source statement for the positive
weighted prime sample norm-square stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Vertical Fourier trace-energy window control at the positive packet owner.
The hypothesis is the exact weighted vertical majorant required for this
finite-window statement. -/
theorem zetaCompletedVerticalPrimeWeightedSample_window_bounded_sourceTraceEnergy
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    ∀ N : ℕ,
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
          N f ≤
        ∑ index in ZetaPrimePowerIndex.window N,
          D * ZetaPrimePowerIndex.polynomialHeightDecay k index := by
  exact
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow_le_weightedVerticalMajorantWindow
      f D k (by exact hbound)

def ZetaCompletedVerticalPrimeWeightedSampleWindowBesselBound
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ D : ℝ, ∃ k : ℕ,
    VerticalPrimeCenterWeightedSpectralPolynomialBound f D k ∧
      ∀ N : ℕ,
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
            N f ≤
          ∑ index in ZetaPrimePowerIndex.window N,
            D * ZetaPrimePowerIndex.polynomialHeightDecay k index

theorem zetaCompletedVerticalPrimeWeightedSampleWindowBesselBound_of_weightedVerticalBound
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    ZetaCompletedVerticalPrimeWeightedSampleWindowBesselBound f := by
  exact ⟨D, k, hbound,
    zetaCompletedVerticalPrimeWeightedSample_window_bounded_sourceTraceEnergy
      f D k hbound⟩

/-- The completed positive prime weighted sample trace-energy scalar. -/
noncomputable def zetaCompletedPrimePositiveWeightedSampleNormSqTraceEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' index : ZetaPrimePowerIndex,
    zetaCompletedPrimePositiveWeightedSampleNormSq index f

/-- Positive weighted prime sample norm-squares are nonnegative. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_nonnegative_sourceTraceEnergy
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimePositiveWeightedSampleNormSq index f := by
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
      index f).symm
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f)

/-- Source packet trace-energy `HasSum` identity for the positive weighted prime
sample norm-square stream. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f)
      (zetaCompletedPrimePositiveWeightedSampleNormSqTraceEnergy f) := by
  have hweighted :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_primitive
      f C₀ k hbound
  have hseries :
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) =
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) := by
    funext index
    exact
      (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
        index f).symm
  have hpositive :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePositiveWeightedSampleNormSq index f)
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    Eq.subst
      (motive := fun series : ZetaPrimePowerIndex → ℝ =>
        HasSum series
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
            f))
      hseries
      hweighted
  unfold zetaCompletedPrimePositiveWeightedSampleNormSqTraceEnergy
  exact hpositive.summable.hasSum

/-- Source packet trace-energy summability for the positive weighted prime
sample norm-square stream. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) := by
  exact
    (zetaCompletedPrimePositiveWeightedSampleNormSq_hasSum_traceEnergy_source
      f C₀ k hbound).summable

/-- Packet-window Bessel trace-energy domination for the positive weighted
prime sample norm-square stream. -/
def ZetaCompletedPrimePositiveWeightedSampleNormSqWindowBesselBound
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ C : ℝ,
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimePositiveWeightedSampleNormSq index f ≤ C

/-- Source packet-window trace-energy domination for the positive weighted
prime sample norm-square stream. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_bounded_sourceTraceEnergy
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    ZetaCompletedPrimePositiveWeightedSampleNormSqWindowBesselBound f := by
  let C : ℝ := zetaCompletedPrimePositiveWeightedSampleNormSqTraceEnergy f
  have hwindow :
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f ≤ C := by
    intro N
    exact
      sum_le_hasSum
        (ZetaPrimePowerIndex.window N)
        (fun index membership =>
          zetaCompletedPrimePositiveWeightedSampleNormSq_nonnegative_sourceTraceEnergy
            index f)
        (zetaCompletedPrimePositiveWeightedSampleNormSq_hasSum_traceEnergy_source
          f C₀ k hbound)
  exact ⟨C, hwindow⟩

/-- The named packet-window Bessel bound unfolds to the concrete finite-window
bound. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_bounded_of_windowBesselBound
    (f : ZetaAdmissibleFunction)
    (hbound :
      ZetaCompletedPrimePositiveWeightedSampleNormSqWindowBesselBound f) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f ≤ C := by
  exact hbound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
