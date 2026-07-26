import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CutoffData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part01_FiniteGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part04_ConcreteCardinalEnvelope

/-!
# Height-window envelope tails

This file owns the monotonic transport from a finite completed-zero cutoff to
the canonical non-dagger height window containing that cutoff.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- A canonical non-dagger height window containing a finite cutoff has no larger
polynomial envelope tail, provided the active completed-zero tail is disjoint from the
fixed dagger sample constraints. -/
theorem zetaCompletedZeroPolynomialEnvelope_heightWindow_tail_le_cutoff_tail
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T : Finset ℂ)
    (R : ℝ)
    (hcover :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))) :
    (∑' ρ : {ρ : ℂ //
      ZetaCompletedZero ρ ∧
        ρ ∉ S ∧
        ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
          (-(k + 3 : ℤ))) ≤
      ∑' ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ T ∧
          ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)) :=
  let α := {ρ : ℂ //
    ZetaCompletedZero ρ ∧
      ρ ∉ S ∧
      ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R}
  let β := {ρ : ℂ //
    ZetaCompletedZero ρ ∧
      ρ ∉ S ∧
      ρ ∉ T ∧
      ρ ∉ daggerClosedSpectralSampleFinset P}
  let envelopeα : α → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
          (-(k + 3 : ℤ))
  let envelopeβ : β → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
          (-(k + 3 : ℤ))
  let zeroMapα : α → {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun ρ => ⟨(ρ : ℂ), ρ.2.1⟩
  let zeroMapβ : β → {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun ρ => ⟨(ρ : ℂ), ρ.2.1⟩
  let inclusion : α → β :=
    fun ρ =>
      ⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1,
        fun hρT =>
          ρ.2.2.2 (hcover (ρ : ℂ) hρT),
        hSeparated (ρ : ℂ) ρ.2.1 ρ.2.2.1⟩
  let hinclusion : Function.Injective inclusion :=
    fun left right heq =>
      Subtype.ext
        (congrArg (fun value : β => (value : ℂ)) heq)
  let hsumα : Summable envelopeα :=
    zetaCompletedZeroPolynomialEnvelope_comp_summable
      A k zeroMapα
      (fun left right heq =>
        Subtype.ext
          (congrArg (fun value : {ρ : ℂ // ZetaCompletedZero ρ} => (value : ℂ)) heq))
      hsum
  let hsumβ : Summable envelopeβ :=
    zetaCompletedZeroPolynomialEnvelope_comp_summable
      A k zeroMapβ
      (fun left right heq =>
        Subtype.ext
          (congrArg (fun value : {ρ : ℂ // ZetaCompletedZero ρ} => (value : ℂ)) heq))
      hsum
  let hnonnegative :
      ∀ ρ : β, 0 ≤ envelopeβ ρ :=
    fun ρ =>
      zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
        (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ})
  tsum_le_tsum_of_inj inclusion hinclusion
    (fun ρ hρ => hnonnegative ρ)
    (fun ρ => le_of_eq (Eq.refl (envelopeα ρ)))
    hsumα hsumβ

/-- A fixed summable polynomial completed-zero envelope has arbitrarily small
complementary mass outside a canonical finite non-dagger height window. -/
theorem exists_zetaCompletedZeroPolynomialEnvelope_nonDaggerHeightWindow_tail_lt
    (S : Finset ℂ)
    (P : Finset ℂ)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉ daggerClosedSpectralSampleFinset P)
    (ε : ℝ)
    (hε : 0 < ε)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))) :
    ∃ R : ℝ,
      (∑' ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ))) < ε :=
  let hemptyZero : ∀ ρ : ℂ, ρ ∈ (∅ : Finset ℂ) → ZetaCompletedZero ρ :=
    fun ρ hρ => False.elim (Finset.not_mem_empty ρ hρ)
  let hemptyOutside : ∀ ρ : ℂ, ρ ∈ (∅ : Finset ℂ) → ρ ∉ S :=
    fun ρ hρ => False.elim (Finset.not_mem_empty ρ hρ)
  let hemptyDagger :
      ∀ ρ : ℂ, ρ ∈ (∅ : Finset ℂ) →
        ρ ∉ daggerClosedSpectralSampleFinset P :=
    fun ρ hρ => False.elim (Finset.not_mem_empty ρ hρ)
  match
    exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported_data
      S P ∅ hemptyZero hemptyOutside hemptyDagger ε hε A k hsum with
  | ⟨T, hemptySubset, hTzero, hTS, hTdagger, hcutoff⟩ =>
      match
          exists_nonDaggerHeightWindow_cover_finite_completedZeros
            S P T hTzero hTS hTdagger
      with
      | ⟨R, hcover⟩ =>
          let hmonotone :
              (∑' ρ : {ρ : ℂ //
                ZetaCompletedZero ρ ∧
                  ρ ∉ S ∧
                  ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                    (-(k + 3 : ℤ))) ≤
                ∑' ρ : {ρ : ℂ //
                  ZetaCompletedZero ρ ∧
                    ρ ∉ S ∧
                    ρ ∉ T ∧
                    ρ ∉ daggerClosedSpectralSampleFinset P},
                  A * zetaCompletedZeroCenteredHeight
                    (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                      (-(k + 3 : ℤ)) :=
            zetaCompletedZeroPolynomialEnvelope_heightWindow_tail_le_cutoff_tail
              S P T R hcover hSeparated A k hA hsum
          ⟨R, lt_of_le_of_lt hmonotone hcutoff⟩

/-- At every cardinal-construction radius, the resulting concrete envelope has a
possibly later canonical height window with arbitrarily small complementary mass. -/
theorem exists_autocorrelationSpectralEvalFiberCardinalEnvelopeData_with_externalHeightTail
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉ daggerClosedSpectralSampleFinset P)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ F : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction,
      ∃ data : AutocorrelationSpectralEvalFiberCardinalEnvelopeData S P f₀ R F,
        ∃ Rtail : ℝ,
          (∑' ρ : {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P Rtail},
            data.envelopeConstant * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                (-(data.envelopeOrder + 3 : ℤ))) < ε :=
  match
    exists_autocorrelationSpectralEvalFiberCardinalEnvelopeData_at_radius
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ R with
  | ⟨F, data⟩ =>
      match
          exists_zetaCompletedZeroPolynomialEnvelope_nonDaggerHeightWindow_tail_lt
            S P hSeparated ε hε data.envelopeConstant data.envelopeOrder
            data.envelopeConstant_nonnegative data.envelopeSummable
      with
      | ⟨Rtail, htail⟩ =>
          ⟨F, data, Rtail, htail⟩

theorem autocorrelationSpectralEvalFiberCardinalEnvelopeData_tail_lt_of_cutoff_before_radius
    (S : Finset ℂ)
    (P : Finset ℂ)
    (R : ℝ)
    (Rtail : ℝ)
    (hRtailR : Rtail ≤ R)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉ daggerClosedSpectralSampleFinset P)
    (f₀ : ZetaAdmissibleFunction)
    (F : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
      ZetaAdmissibleFunction)
    (data : AutocorrelationSpectralEvalFiberCardinalEnvelopeData S P
      f₀ R F)
    (ε : ℝ)
    (htail :
      (∑' ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P Rtail},
        data.envelopeConstant * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(data.envelopeOrder + 3 : ℤ))) < ε) :
    (∑' ρ : {ρ : ℂ //
      ZetaCompletedZero ρ ∧
        ρ ∉ S ∧
        ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
      data.envelopeConstant * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
          (-(data.envelopeOrder + 3 : ℤ))) < ε :=
  let hcover :
      ∀ ρ : ℂ, ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P Rtail →
        ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R :=
    autocorrelationSpectralEvalFiberNonDaggerHeightWindow_mono S P hRtailR
  let hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          data.envelopeConstant * zetaCompletedZeroCenteredHeight ρ ^
            (-(data.envelopeOrder + 3 : ℤ))) :=
    data.envelopeSummable
  let hle :
      (∑' ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
        data.envelopeConstant * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(data.envelopeOrder + 3 : ℤ))) ≤
        ∑' ρ : {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P Rtail ∧
            ρ ∉ daggerClosedSpectralSampleFinset P},
          data.envelopeConstant * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(data.envelopeOrder + 3 : ℤ)) :=
    zetaCompletedZeroPolynomialEnvelope_heightWindow_tail_le_cutoff_tail
      S P
      (autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P Rtail)
      R
      hcover
      hSeparated
      data.envelopeConstant
      data.envelopeOrder
      data.envelopeConstant_nonnegative
      hsum
  lt_of_le_of_lt hle htail

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
