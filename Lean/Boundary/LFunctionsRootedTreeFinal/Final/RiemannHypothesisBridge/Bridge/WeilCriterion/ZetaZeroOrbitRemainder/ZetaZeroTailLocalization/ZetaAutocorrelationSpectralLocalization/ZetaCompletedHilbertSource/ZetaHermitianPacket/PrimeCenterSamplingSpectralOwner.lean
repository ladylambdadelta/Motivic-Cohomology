import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDensityDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingWeightBound

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-! ### Vertical sampling majorant owner

The old `PrimeCenterSpectralPolynomialBound` belongs to the real-Laplace
compatibility lane.  The corrected Fourier lane gets a separate predicate so
that its analytic sample is never silently identified with that incompatible
real-axis transform. -/

def VerticalPrimeCenterSpectralPolynomialBound
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ) : Prop :=
  ∀ ι : ZetaPrimePowerIndex,
    completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
        ι f ≤
      D * ZetaPrimePowerIndex.polynomialHeightDecay k ι

theorem verticalPrimeCenterSpectralPolynomialBound_iff
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ) :
    VerticalPrimeCenterSpectralPolynomialBound f D k ↔
      ∀ ι : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
            ι f ≤
          D * ZetaPrimePowerIndex.polynomialHeightDecay k ι :=
  Iff.rfl

/-! The weighted predicate is the exact interface needed by summability and
finite-subtrace owners.  It is stated separately because the arithmetic step
which absorbs the prime-power weight is not part of vertical Fourier decay. -/

def VerticalPrimeCenterWeightedSpectralPolynomialBound
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ) : Prop :=
  ∀ ι : ZetaPrimePowerIndex,
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
        ι f ≤
      D * ZetaPrimePowerIndex.polynomialHeightDecay k ι

theorem verticalPrimeCenterWeightedSpectralPolynomialBound_iff
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ) :
    VerticalPrimeCenterWeightedSpectralPolynomialBound f D k ↔
      ∀ ι : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
            ι f ≤
          D * ZetaPrimePowerIndex.polynomialHeightDecay k ι :=
  Iff.rfl

theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_weightedVerticalBound
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f) := by
  exact
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_majorant
      f D k hbound

theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow_le_weightedVerticalMajorantWindow
    (f : ZetaAdmissibleFunction) (D : ℝ) (k N : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
        N f ≤
      ∑ ι in ZetaPrimePowerIndex.window N,
        D * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow_le_majorantWindow
      N f D k hbound

theorem completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity_decay_owner_export
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
            ι f ≤
          (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := by
  exact completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity_decay_owner
    f N

/-- Canonical sampling-owner export for the corrected vertical Fourier lane. -/
theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_majorant_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : ∀ ι : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f ≤
        D * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f) := by
  exact
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_majorant
      f D k hbound

theorem verticalPrimeCenterWeightedSpectralPolynomialBound_of_verticalDensityBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity : ∀ index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          index f ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧ VerticalPrimeCenterWeightedSpectralPolynomialBound f D l := by
  match
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_bound_of_verticalDensity_bound_owner
      f C k hC hdensity with
  | ⟨D, l, hD, hbound⟩ =>
      exact ⟨D, l, hD, hbound⟩

/-- The arithmetic owner cut for the prime-center polynomial estimate.

The Paley--Wiener envelope estimate is analytic, while the displayed
polynomial envelope inequality is the separate prime-height input.  Keeping
that cut here lets all downstream sampling owners consume one named theorem
without silently turning the arithmetic input into an unconditional claim.
-/
theorem primeCenterSpectralPolynomialBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (henvelope : ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          f (canonicalZetaPaleyWienerSupportInterval f)
          index.center index.center ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    PrimeCenterSpectralPolynomialBound f C k :=
  primeCenterSpectralPolynomialBound_of_canonicalEnvelope_polynomialBound
    f C k hC henvelope

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_of_spectralPolynomialBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact weightedPrimeSampling_summable_of_spectralPolynomialBound f C k hbound

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ B : ℝ, ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ B := by
  exact weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound
    f C k hbound

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_upperBound_of_spectralPolynomialBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ B : ℝ, ∀ N : ℕ,
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
        N f ≤ B := by
  match weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound
      f C k hbound with
  | ⟨B, hB⟩ =>
      exact ⟨B, fun N => Eq.subst
        (motive := fun value : ℝ => value ≤ B)
        (sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_window
          N f)
        (hB (ZetaPrimePowerIndex.box N))⟩

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_upperBound_of_spectralPolynomialBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ B : ℝ, ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ B := by
  match
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound_owner
        f C k hbound with
  | ⟨B, hB⟩ =>
      exact ⟨B, fun N => hB (ZetaPrimePowerIndex.box N)⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
