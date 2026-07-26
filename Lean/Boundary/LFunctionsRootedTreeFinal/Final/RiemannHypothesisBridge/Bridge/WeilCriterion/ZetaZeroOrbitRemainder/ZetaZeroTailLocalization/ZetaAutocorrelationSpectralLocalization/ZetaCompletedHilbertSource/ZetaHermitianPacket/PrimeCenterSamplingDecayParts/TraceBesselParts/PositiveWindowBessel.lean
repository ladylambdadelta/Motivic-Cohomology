import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime positive genuine-window Bessel source

This file owns genuine-window Bessel domination for the positive weighted
prime sample norm-square stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Positive completed weighted sample norm-squares are nonnegative. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_nonnegative_bessel_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimePositiveWeightedSampleNormSq index f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
      index f).symm
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f)

/-- Source genuine-window Bessel domination for the positive weighted prime
sample norm-square stream. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_bessel_source_primitive
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_source
      f with
  | ⟨C, hC⟩ =>
      let hwindow :
          ∀ N : ℕ,
            ∑ index in ZetaPrimePowerIndex.window N,
              zetaCompletedPrimePositiveWeightedSampleNormSq index f ≤ C :=
        fun N =>
        let hsum :
            (∑ index in ZetaPrimePowerIndex.window N,
              zetaCompletedPrimePositiveWeightedSampleNormSq index f) =
              ∑ index in ZetaPrimePowerIndex.window N,
                completedAutocorrelationSpectralTransform_weightedPrimeSampling
                  index f :=
          Finset.sum_congr
            (Eq.refl (ZetaPrimePowerIndex.window N))
            (fun index membership =>
              zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
                index f)
        Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          hsum.symm
          (hC (ZetaPrimePowerIndex.window N))
      Exists.intro C hwindow

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
