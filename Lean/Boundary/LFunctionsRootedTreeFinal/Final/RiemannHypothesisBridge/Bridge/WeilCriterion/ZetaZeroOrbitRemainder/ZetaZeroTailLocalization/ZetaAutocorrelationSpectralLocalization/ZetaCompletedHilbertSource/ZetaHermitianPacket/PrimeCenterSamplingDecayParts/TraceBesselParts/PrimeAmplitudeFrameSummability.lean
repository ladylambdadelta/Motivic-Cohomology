import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingBesselSource
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Prime amplitude frame summability source

This file owns square-summability for the completed prime spectral amplitude
coordinate family.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The finite completed prime amplitude projection energy over a finite
prime-power index set. -/
noncomputable def zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2

/-- The finite completed prime amplitude projection energy unfolds to its
finite sum. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
        s f =
      ∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Eq.refl
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
      s f)

/-- Completed prime spectral amplitude coordinate squares are nonnegative. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_nonnegative_frame_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  sq_nonneg ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖

/-- Source upper-bound package for finite completed prime amplitude projection
energies.  This is the analytic Hilbert-frame Bessel primitive. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_upperBound_frame_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
          s f ≤ C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_traceEnergy_source
      f C k hbound with
  | ⟨C, hC⟩ =>
      let hbound :
          ∀ s : Finset ZetaPrimePowerIndex,
            zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
              s f ≤ C :=
        fun s =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum
            s f).symm
          (hC s)
      Exists.intro C hbound

/-- Source boundedness of the finite completed prime amplitude projection
energy range. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_frame_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
            s f)) :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_upperBound_frame_source
      f C k hbound with
  | ⟨C, hC⟩ =>
      let hupper :
          ∀ value : ℝ,
            value ∈
              Set.range
                (fun s : Finset ZetaPrimePowerIndex =>
                  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
                    s f) →
            value ≤ C :=
        fun value hvalue =>
        match hvalue with
        | ⟨s, hvalue_eq⟩ =>
            Eq.subst
              (motive := fun projectionValue : ℝ => projectionValue ≤ C)
              hvalue_eq
              (hC s)
      Exists.intro C hupper

/-- Finite-subtrace Hilbert-frame Bessel domination for completed prime
spectral amplitude coordinate squares. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_frame_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_traceEnergy_source
    f C k hbound

/-- Finite-subtrace Bessel domination gives square-summability of the
completed prime spectral amplitude coordinate family. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_finiteSubtrace_bessel_frame_source
    (f : ZetaAdmissibleFunction)
    (hfinite :
      ∃ C : ℝ,
        ∀ s : Finset ZetaPrimePowerIndex,
          ∑ index in s,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    fun index =>
      zetaCompletedPrimeSpectralAmplitudeIndex_normSq_nonnegative_frame_source
        index f
  match hfinite with
  | ⟨C, hC⟩ =>
      summable_of_sum_le hnonnegative hC

noncomputable def zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy s f =
      ∑ index in s,
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2 :=
  Eq.refl
    (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy s f)

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
          s f ≤ C := by
  exact ⟨zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy f,
    fun s =>
      Eq.subst
        (motive := fun value : ℝ => value ≤
          zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy f)
        (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum
          s f).symm
        (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
          f D k hbound s)⟩

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_owner
    f D k hbound

noncomputable def zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy s f =
      ∑ index in s,
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Eq.refl
    (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
      s f)

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
          s f ≤ C := by
  exact ⟨zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy f,
    fun s =>
      Eq.subst
        (motive := fun value : ℝ => value ≤
          zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy f)
        (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum
          s f).symm
        (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
          f D k hbound s)⟩

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_owner
    f D k hbound

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_hasSum_tsum_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2)
      (∑' index : ZetaPrimePowerIndex,
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_frame_source
    f D k hbound).hasSum

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_hasSum_tsum_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2)
      (∑' index : ZetaPrimePowerIndex,
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_frame_source
    f D k hbound).hasSum

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
            s f)) := by
  match zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_frame_source
      f D k hbound with
  | ⟨C, hC⟩ =>
      exact ⟨C,
        fun value hvalue =>
          match hvalue with
          | ⟨s, hvalue_eq⟩ =>
              Eq.subst
                (motive := fun projectionValue : ℝ => projectionValue ≤ C)
                hvalue_eq
                (hC s)⟩

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_frame_source
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
            s f)) := by
  match zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_frame_source
      f D k hbound with
  | ⟨C, hC⟩ =>
      exact ⟨C,
        fun value hvalue =>
          match hvalue with
          | ⟨s, hvalue_eq⟩ =>
              Eq.subst
                (motive := fun projectionValue : ℝ => projectionValue ≤ C)
                hvalue_eq
                (hC s)⟩

/-- Hilbert-frame square summability for the completed prime spectral
amplitude coordinate family. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_frame_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
    f C k hbound

/-- The completed prime spectral amplitude coordinate square series has sum
equal to its `tsum`. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_hasSum_tsum_frame_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2)
      (∑' index : ZetaPrimePowerIndex,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_frame_source
    f C k hbound).hasSum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
