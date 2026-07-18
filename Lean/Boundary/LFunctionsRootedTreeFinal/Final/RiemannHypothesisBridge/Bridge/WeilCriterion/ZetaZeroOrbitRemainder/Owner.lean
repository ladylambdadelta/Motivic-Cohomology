import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaWeilShared.Owner

/-!
# Boundary zero-side orbit remainder

This file packages the orbit remainder as the tail specialized to the orbit of
the chosen zero.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The orbit remainder is the tail after removing the orbit of the chosen zero. -/
theorem zetaZeroOrbitRemainder_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainder ρ φ =
      zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
  rfl

/-- The real-valued orbit remainder is the real part of the complex one. -/
theorem zetaZeroOrbitRemainderRe_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainderRe ρ φ =
      Complex.re (zetaZeroOrbitRemainder ρ φ) := by
  rfl

variable
  (hZeroTailSmallValuesOwnerRunge :
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      (∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
            r < ε)

include hZeroTailSmallValuesOwnerRunge

/-- Localizing around a finite-orbit negative-margin autocorrelation probe preserves that
margin and makes the orbit remainder arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_remainder_small_near_margin_probe
    (ρ : ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ η : ℂ,
        ZetaCompletedZero η →
          η ∉ zetaZeroOrbitFinset ρ →
            η ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
                (zetaZeroOrbitFinset ρ))
    (hmargin :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) ≤ -δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ ∧
          |zetaZeroOrbitRemainderRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε := by
  exact exists_zeroOrbit_autocorrelation_remainder_small_near_margin_probe_owner
    hZeroTailSmallValuesOwnerRunge ρ δ hδ f₀ hSeparated hmargin

/-- Tail localization preserves a fixed finite-orbit negative margin while making the
orbit remainder arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_remainder_small_preserving_margin
    (ρ : ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hSeparated :
      ∀ η : ℂ,
        ZetaCompletedZero η →
          η ∉ zetaZeroOrbitFinset ρ →
            η ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
                (zetaZeroOrbitFinset ρ))
    (hmargin :
      ∀ ε : ℝ, 0 < ε →
        ∃ f : ZetaAdmissibleFunction,
          zetaZeroOrbitContributionRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ ∧
          |zetaZeroOrbitRemainderRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε := by
  match hmargin 1 zero_lt_one with
  | ⟨f₀, hf₀⟩ =>
    exact exists_zeroOrbit_autocorrelation_remainder_small_near_margin_probe
      hZeroTailSmallValuesOwnerRunge ρ δ hδ f₀ hSeparated hf₀

/-- Combining a fixed finite-orbit margin with margin-preserving tail localization gives
the uniform separator family. -/
theorem exists_uniform_zeroOrbit_autocorrelation_separator_of_margin_family
    (ρ : ℂ)
    (hSeparated :
      ∀ η : ℂ,
        ZetaCompletedZero η →
          η ∉ zetaZeroOrbitFinset ρ →
            η ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
                (zetaZeroOrbitFinset ρ))
    (hmargin :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ f : ZetaAdmissibleFunction,
            zetaZeroOrbitContributionRe ρ
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ f : ZetaAdmissibleFunction,
          zetaZeroOrbitContributionRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ ∧
            |zetaZeroOrbitRemainderRe ρ
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε := by
  match hmargin with
  | ⟨δ, hδ, hfamily⟩ =>
    exact ⟨δ, hδ,
      exists_zeroOrbit_autocorrelation_remainder_small_preserving_margin
        hZeroTailSmallValuesOwnerRunge ρ δ hδ hSeparated hfamily⟩

/-- Uniform off-critical zero-orbit separation by admissible autocorrelation probes. -/
theorem exists_uniform_zeroOrbit_autocorrelation_separator
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η)
    (hSeparated :
      ∀ η : ℂ,
        ZetaCompletedZero η →
          η ∉ zetaZeroOrbitFinset ρ →
            η ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
                (zetaZeroOrbitFinset ρ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ f : ZetaAdmissibleFunction,
          zetaZeroOrbitContributionRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ ∧
            |zetaZeroOrbitRemainderRe ρ
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε := by
  exact exists_uniform_zeroOrbit_autocorrelation_separator_of_margin_family
    hZeroTailSmallValuesOwnerRunge ρ hSeparated
    (exists_zeroOrbit_autocorrelation_negative_margin_family
      ρ hρ hρre horbit)

omit hZeroTailSmallValuesOwnerRunge

/-- A real negative margin and an absolute tail bound dominate the tail by the margin. -/
theorem remainder_lt_neg_of_le_neg_margin_and_abs_lt_margin
    {A R δ : ℝ} (hδ : 0 < δ) (hA : A ≤ -δ) (hR : |R| < δ) :
    A < 0 ∧ R < -A := by
  have hAneg : A < 0 :=
    lt_of_le_of_lt hA (neg_lt_zero.mpr hδ)
  have hRltδ : R < δ :=
    (abs_lt.mp hR).2
  have hδle : δ ≤ -A := by
    calc
      δ = -(-δ) := (neg_neg δ).symm
      _ ≤ -A := neg_le_neg hA
  exact ⟨hAneg, lt_of_lt_of_le hRltδ hδle⟩

/-- Uniform finite-orbit separation with arbitrarily small tail gives the final
finite-orbit/tail domination statement. -/
theorem exists_negative_with_dominated_remainder_of_uniform_margin
    {α : Type} (A R : α → ℝ)
    (h :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ x : α, A x ≤ -δ ∧ |R x| < ε) :
    ∃ x : α, A x < 0 ∧ R x < -A x := by
  match h with
  | ⟨δ, hδ, hprobe⟩ =>
    match hprobe δ hδ with
    | ⟨x, hA, hR⟩ =>
      exact ⟨x, remainder_lt_neg_of_le_neg_margin_and_abs_lt_margin hδ hA hR⟩

/-- Uniform zero-orbit separation gives a finite negative contribution whose remainder is
dominated by that negative margin. -/
theorem exists_negative_zeroOrbit_with_dominated_remainder_autocorrelation
    (ρ : ℂ)
    (h :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ f : ZetaAdmissibleFunction,
            zetaZeroOrbitContributionRe ρ
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ ∧
              |zetaZeroOrbitRemainderRe ρ
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε) :
    ∃ f : ZetaAdmissibleFunction,
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 ∧
        zetaZeroOrbitRemainderRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) <
            - zetaZeroOrbitContributionRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact exists_negative_with_dominated_remainder_of_uniform_margin
    (fun f : ZetaAdmissibleFunction =>
      zetaZeroOrbitContributionRe ρ
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (fun f : ZetaAdmissibleFunction =>
      zetaZeroOrbitRemainderRe ρ
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    h

/-- A tail dominated by the negative of the finite contribution makes the sum negative. -/
theorem zeroOrbit_add_remainder_lt_zero_of_remainder_lt_neg
    {A R : ℝ} (hR : R < -A) :
    A + R < 0 := by
  have hsum_lt : A + R < A + -A :=
    add_lt_add_left hR A
  exact hsum_lt.trans_eq (add_neg_cancel A)

/-- Complex zero-side excision for the functional-equation orbit of one zero. -/
theorem zetaCompletedZeroSideSum_eq_orbitContribution_add_orbitRemainder
    (ρ : ℂ) (φ : ZetaAdmissibleFunction)
    (_hρ : ZetaCompletedZero ρ)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η)
    (hsum :
      Summable
        (fun η : {η : ℂ // ZetaCompletedZero η} =>
          zetaZeroSideContribution (η : ℂ) φ)) :
    (∑' η : {η : ℂ // ZetaCompletedZero η},
        zetaZeroSideContribution (η : ℂ) φ) =
      zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ := by
  have htail :
      (∑' η : {η : ℂ // ZetaCompletedZero η},
          zetaZeroSideContribution (η : ℂ) φ) =
        (∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ) +
          zetaZeroTail (zetaZeroOrbitFinset ρ) φ :=
    zetaCompletedZeroSideSum_eq_finite_add_tail
      (zetaZeroOrbitFinset ρ) φ horbit hsum
  have horbit_sum :
      zetaZeroOrbitContribution ρ φ =
        ∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ :=
    zetaZeroOrbitContribution_eq_sum ρ φ
  have hremainder :
      zetaZeroOrbitRemainder ρ φ =
        zetaZeroTail (zetaZeroOrbitFinset ρ) φ :=
    zetaZeroOrbitRemainder_eq ρ φ
  calc
    (∑' η : {η : ℂ // ZetaCompletedZero η},
        zetaZeroSideContribution (η : ℂ) φ) =
        (∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ) +
          zetaZeroTail (zetaZeroOrbitFinset ρ) φ := htail
    _ = zetaZeroOrbitContribution ρ φ +
          zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
      exact congrArg
        (fun x : ℂ => x + zetaZeroTail (zetaZeroOrbitFinset ρ) φ)
        horbit_sum.symm
    _ = zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ := by
      exact congrArg
        (fun x : ℂ => zetaZeroOrbitContribution ρ φ + x)
        hremainder.symm

/-- The completed zero-side real scalar splits into the chosen finite zero orbit and the
complementary orbit remainder.

This is the zero-side owner decomposition: after a finite functional-equation orbit has been
isolated, the completed zero-side `tsum` is the finite orbit contribution plus the tail over
all remaining zeros. -/
theorem zetaCompletedZeroSideRe_eq_orbitContribution_add_orbitRemainderRe
    (ρ : ℂ) (φ : ZetaAdmissibleFunction)
    (hρ : ZetaCompletedZero ρ)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η)
    (hsum :
      Summable
        (fun η : {η : ℂ // ZetaCompletedZero η} =>
          zetaZeroSideContribution (η : ℂ) φ)) :
    zetaCompletedZeroSideRe φ =
      zetaZeroOrbitContributionRe ρ φ + zetaZeroOrbitRemainderRe ρ φ := by
  have hcomplex :
      (∑' η : {η : ℂ // ZetaCompletedZero η},
          zetaZeroSideContribution (η : ℂ) φ) =
        zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ :=
    zetaCompletedZeroSideSum_eq_orbitContribution_add_orbitRemainder
      ρ φ hρ horbit hsum
  unfold zetaCompletedZeroSideRe
  unfold zetaZeroOrbitContributionRe
  unfold zetaZeroOrbitRemainderRe
  calc
    Complex.re
        (∑' η : {η : ℂ // ZetaCompletedZero η},
          zetaZeroSideContribution (η : ℂ) φ) =
        Complex.re (zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ) := by
      exact congrArg Complex.re hcomplex
    _ = Complex.re (zetaZeroOrbitContribution ρ φ) +
          Complex.re (zetaZeroOrbitRemainder ρ φ) := by
      exact Complex.add_re
        (zetaZeroOrbitContribution ρ φ)
        (zetaZeroOrbitRemainder ρ φ)

/-- The orbit/remainder decomposition transports negativity to the completed zero side. -/
theorem zetaCompletedZeroSideRe_lt_zero_of_orbitContribution_add_remainderRe_lt_zero
    (ρ : ℂ) (φ : ZetaAdmissibleFunction)
    (hρ : ZetaCompletedZero ρ)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η)
    (hsum :
      Summable
        (fun η : {η : ℂ // ZetaCompletedZero η} =>
          zetaZeroSideContribution (η : ℂ) φ))
    (hneg :
      zetaZeroOrbitContributionRe ρ φ +
        zetaZeroOrbitRemainderRe ρ φ < 0) :
    zetaCompletedZeroSideRe φ < 0 := by
  exact Eq.subst
    (motive := fun x : ℝ => x < 0)
    (zetaCompletedZeroSideRe_eq_orbitContribution_add_orbitRemainderRe
      ρ φ hρ horbit hsum).symm
    hneg

/-- A dagger-closed completed-zero window around a completed zero gives a
negative completed zero side after localizing its complementary tail.

The finite window is deliberately larger than the two-point functional-equation
orbit: it contains every completed-zero point forced by the autocorrelation
dagger symmetry. -/
theorem exists_negative_completedZeroSide_autocorrelation_of_daggerClosedOrbitWindow
    (hZeroTailSmallValuesOwnerRunge :
      ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
        (∀ z : ℂ,
          ZetaCompletedZero z →
            z ∉ S →
              z ∉ ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) →
        ∀ ε : ℝ, 0 < ε →
          ∃ r : ℝ,
            r ∈ ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
              r < ε)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideRe
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  match exists_daggerClosedOrbit_autocorrelation_unitSpectralSamples ρ with
  | ⟨f₀, hf₀⟩ =>
      let S : Finset ℂ := zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ
      let P : Finset ℂ := zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ
      let φ₀ : ZetaAdmissibleFunction :=
        ZetaAdmissibleFunction.convolutionAutocorrelation f₀
      have hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η := by
        intro η hη
        exact zetaZeroOrbitDaggerClosedCompletedZeroFinset_mem_completedZero ρ η hη
      have hρS : ρ ∈ S :=
        zetaZero_mem_zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ hρ
      have hsample₀ : ∀ η : ℂ, η ∈ S → zetaSpectralEval φ₀ η = 1 := by
        intro η hη
        have hηP : η ∈ P := by
          exact mem_zetaZeroOrbitDaggerClosedSpectralSampleFinset_of_mem_completedWindow
            ρ η hη
        exact hf₀ η hηP
      have hfinite₀ :
          Complex.re (∑ η in S, zetaZeroSideContribution η φ₀) < 0 :=
        finiteCompletedZeroContributionRe_lt_zero_of_unitSpectralSamples
          S hS ρ hρS φ₀ hsample₀
      have hmargin : 0 < -Complex.re (∑ η in S, zetaZeroSideContribution η φ₀) :=
        neg_pos.mpr hfinite₀
      match
        exists_daggerClosedOrbit_autocorrelation_unitSamples_zeroTail_small
          hZeroTailSmallValuesOwnerRunge
          ρ
          (-Complex.re (∑ η in S, zetaZeroSideContribution η φ₀))
          hmargin with
      | ⟨f, hsample, htail⟩ =>
          let φ : ZetaAdmissibleFunction :=
            ZetaAdmissibleFunction.convolutionAutocorrelation f
          have hfinite_eq :
              (∑ η in S, zetaZeroSideContribution η φ) =
                ∑ η in S, zetaZeroSideContribution η φ₀ := by
            exact Finset.sum_congr rfl (fun η hη =>
              zetaZeroSideContribution_eq_of_spectralEval_eq
                η φ φ₀
                (Eq.trans (hsample η hη) (hsample₀ η hη).symm))
          have htail_lt :
              Complex.re (zetaZeroTail S φ) <
                -Complex.re (∑ η in S, zetaZeroSideContribution η φ) := by
            have htail_upper :
                Complex.re (zetaZeroTail S φ) <
                  -Complex.re (∑ η in S, zetaZeroSideContribution η φ₀) :=
              (abs_lt.mp htail).2
            exact Eq.subst
              (motive := fun x : ℝ =>
                Complex.re (zetaZeroTail S φ) < -x)
              (congrArg Complex.re hfinite_eq).symm
              htail_upper
          have hsum :
              Summable
                (fun η : {η : ℂ // ZetaCompletedZero η} =>
                  zetaZeroSideContribution (η : ℂ) φ) :=
            summable_zetaZeroSideContribution
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary φ
          have hsplit :
              zetaCompletedZeroSideRe φ =
                Complex.re (∑ η in S, zetaZeroSideContribution η φ) +
                  Complex.re (zetaZeroTail S φ) := by
            have hcomplex := zetaCompletedZeroSideSum_eq_finite_add_tail S φ hS hsum
            unfold zetaCompletedZeroSideRe
            calc
              Complex.re
                  (∑' η : {η : ℂ // ZetaCompletedZero η},
                    zetaZeroSideContribution (η : ℂ) φ) =
                  Complex.re
                    ((∑ η in S, zetaZeroSideContribution η φ) + zetaZeroTail S φ) := by
                      exact congrArg Complex.re hcomplex
              _ = Complex.re (∑ η in S, zetaZeroSideContribution η φ) +
                    Complex.re (zetaZeroTail S φ) := by
                      exact Complex.add_re
                        (∑ η in S, zetaZeroSideContribution η φ)
                        (zetaZeroTail S φ)
          have hnegative :
              Complex.re (∑ η in S, zetaZeroSideContribution η φ) +
                Complex.re (zetaZeroTail S φ) < 0 := by
            exact zeroOrbit_add_remainder_lt_zero_of_remainder_lt_neg htail_lt
          exact ⟨f, Eq.subst (motive := fun x : ℝ => x < 0) hsplit.symm hnegative⟩

end
end LFunctions
end Boundary
