import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.FiniteSubtraceOwner
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Completed weighted prime sampling finite Bessel source

This file owns the noncircular analytic Bessel input for the completed
weighted prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- The Hilbert-frame trace energy of the completed weighted prime-center
sampling stream. -/
noncomputable def completedWeightedPrimeSamplingTraceEnergy_hilbertFrame
    (f : ZetaAdmissibleFunction) : ℝ :=
  sSup
    (Set.range
      (fun s : Finset ZetaPrimePowerIndex =>
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f))

/-- The Hilbert-frame trace energy is the least upper bound of finite
completed weighted prime-center projection energies. -/
theorem completedWeightedPrimeSamplingTraceEnergy_isLUB_projectionEnergy_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    IsLUB
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
            s f))
      (completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f) :=
  isLUB_csSup
    (completedWeightedPrimeSamplingProjectionEnergy_range_nonempty_hilbertFrame
      f)
    (completedWeightedPrimeSamplingProjectionEnergy_bddAbove_owner
      f)

/-- The projection-energy function equals its finite-sum presentation. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_function_eq_sum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    (fun s : Finset ZetaPrimePowerIndex =>
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f) =
    (fun s : Finset ZetaPrimePowerIndex =>
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  funext
    (fun s : Finset ZetaPrimePowerIndex =>
      completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
        s f)

/-- The finite projection-energy LUB transfers to the finite-sum presentation. -/
theorem completedWeightedPrimeSamplingTraceEnergy_isLUB_finiteSum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    IsLUB
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          ∑ index in s,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f))
      (completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f) :=
  Eq.subst
    (motive :=
      fun projection : Finset ZetaPrimePowerIndex → ℝ =>
        IsLUB
          (Set.range projection)
          (completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f))
    (completedWeightedPrimeSamplingProjectionEnergy_function_eq_sum_hilbertFrame_source
      f)
    (completedWeightedPrimeSamplingTraceEnergy_isLUB_projectionEnergy_hilbertFrame_source
      f)

/-- Source trace-energy reconstruction for the completed weighted prime-center
sampling stream.  This is the analytic Hilbert-frame Bessel input before
diagonal-debt spectral majorants are available. -/
theorem completedWeightedPrimeSampling_hasSum_traceEnergy_hilbertFrame_source_primitive
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f) :=
  hasSum_of_isLUB_of_nonneg
    (completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f)
    (fun index : ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f)
    (completedWeightedPrimeSamplingTraceEnergy_isLUB_finiteSum_hilbertFrame_source
      f)

/-- Source summability of the completed weighted prime-center sampling stream,
as a consequence of trace-energy reconstruction. -/
theorem completedWeightedPrimeSampling_summable_of_traceEnergy_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  (completedWeightedPrimeSampling_hasSum_traceEnergy_hilbertFrame_source_primitive
    f).summable

/-- The completed weighted prime-center sampling stream has its `tsum`. -/
theorem completedWeightedPrimeSampling_hasSum_tsum_of_traceEnergy_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (∑' index : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  (completedWeightedPrimeSampling_summable_of_traceEnergy_hilbertFrame_source
    f).hasSum

/-- The Hilbert-frame trace energy is the `tsum` of the completed weighted
prime-center sampling stream after trace-energy reconstruction. -/
theorem completedWeightedPrimeSamplingTraceEnergy_eq_tsum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f =
      ∑' index : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  (completedWeightedPrimeSampling_hasSum_traceEnergy_hilbertFrame_source_primitive
    f).tsum_eq.symm

/-- The completed weighted prime-center sampling stream is nonnegative. -/
theorem completedWeightedPrimeSampling_nonnegative_finiteBessel_source
    (f : ZetaAdmissibleFunction) :
    ∀ index : ZetaPrimePowerIndex,
      0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f :=
  fun index : ZetaPrimePowerIndex =>
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f

/-- Every finite completed weighted prime-center sampling subtrace is bounded
by the reconstructed trace energy of the summable stream. -/
theorem completedWeightedPrimeSampling_finiteSubtrace_le_traceEnergy_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤
        completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f :=
  fun s : Finset ZetaPrimePowerIndex =>
    sum_le_hasSum
      s
      (fun index membership =>
        completedWeightedPrimeSampling_nonnegative_finiteBessel_source
          f index)
      (completedWeightedPrimeSampling_hasSum_traceEnergy_hilbertFrame_source_primitive
        f)

/-- Source finite-subtrace Bessel domination for the completed weighted
prime-center sampling stream.  This is the analytic Hilbert-frame input needed
before diagonal-debt spectral majorants are constructed. -/
theorem completedWeightedPrimeSamplingFiniteSubtraceBound_hilbertFrame_source_primitive
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  ⟨completedWeightedPrimeSamplingTraceEnergy_hilbertFrame f,
    completedWeightedPrimeSampling_finiteSubtrace_le_traceEnergy_hilbertFrame_source
      f⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
