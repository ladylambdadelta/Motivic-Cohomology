import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroOrbitContribution.ZetaZeroSpectralSeparation.Owner

/-!
# Zero-tail localization

This file owns the localization step that keeps a fixed finite-orbit negative
margin while making the complementary zero-tail contribution arbitrarily small.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- If two probes have the same spectral evaluation at one centered zero coordinate, then
their single zero-side contributions at that zero agree. -/
theorem zetaZeroSideContribution_eq_of_spectralEval_eq
    (η : ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      zetaSpectralEval φ η =
        zetaSpectralEval ψ η) :
    zetaZeroSideContribution η φ =
      zetaZeroSideContribution η ψ := by
  calc
    zetaZeroSideContribution η φ =
        - (zetaZeroMultiplicity η : ℂ) *
          zetaSpectralEval φ η := by
      exact zetaZeroSideContribution_def η φ
    _ =
        - (zetaZeroMultiplicity η : ℂ) *
          zetaSpectralEval ψ η := by
      exact congrArg
        (fun z : ℂ => - (zetaZeroMultiplicity η : ℂ) * z)
        hsample
    _ = zetaZeroSideContribution η ψ := by
      exact (zetaZeroSideContribution_def η ψ).symm

/-- If two probes have the same spectral evaluations on the centered zero orbit, then their
complex finite orbit contributions agree. -/
theorem zetaZeroOrbitContribution_eq_of_spectralEval_eq_on_orbit
    (ρ : ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ η =
          zetaSpectralEval ψ η) :
    zetaZeroOrbitContribution ρ φ =
      zetaZeroOrbitContribution ρ ψ := by
  unfold zetaZeroOrbitContribution
  exact Finset.sum_congr rfl
    (fun η hη =>
      zetaZeroSideContribution_eq_of_spectralEval_eq
        η φ ψ (hsample η hη))

/-- If two probes have the same spectral evaluations on the centered zero orbit, then their
finite orbit contributions agree. -/
theorem zetaZeroOrbitContributionRe_eq_of_spectralEval_eq_on_orbit
    (ρ : ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ η =
          zetaSpectralEval ψ η) :
    zetaZeroOrbitContributionRe ρ φ =
      zetaZeroOrbitContributionRe ρ ψ := by
  exact congrArg Complex.re
    (zetaZeroOrbitContribution_eq_of_spectralEval_eq_on_orbit
      ρ φ ψ hsample)

/-- The finite spectral sample set attached to a finite set of completed-zero coordinates. -/
def zetaZeroTailSpectralSampleFinset
    (S : Finset ℂ) : Finset ℂ :=
  S

/-- A completed-zero coordinate in the finite tail-exclusion set belongs to the
associated finite spectral sample set. -/
theorem completedZero_mem_zeroTailSpectralSampleFinset
    (S : Finset ℂ) (η : ℂ) (hη : η ∈ S) :
    η ∈ zetaZeroTailSpectralSampleFinset S := by
  unfold zetaZeroTailSpectralSampleFinset
  exact hη

/-- Equality on the finite centered spectral sample set gives equality on the original
zero-coordinate sample set. -/
theorem zeroTailSpectralSample_eq_on_zeroSet_of_eq_on_sampleFinset
    (S : Finset ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      ∀ z : ℂ, z ∈ zetaZeroTailSpectralSampleFinset S →
        zetaSpectralEval φ z = zetaSpectralEval ψ z) :
    ∀ η : ℂ, η ∈ S →
      zetaSpectralEval φ η =
        zetaSpectralEval ψ η := by
  intro η hη
  exact hsample
    η
    (completedZero_mem_zeroTailSpectralSampleFinset S η hη)

/-- The orbit spectral sample set is the zero-tail spectral sample set of the orbit. -/
theorem zetaZeroTailSpectralSampleFinset_orbit
    (ρ : ℂ) :
    zetaZeroTailSpectralSampleFinset (zetaZeroOrbitFinset ρ) =
      zetaZeroOrbitFinset ρ := by
  rfl

/-- Equality on the centered spectral sample set of a zero orbit gives equality on the
orbit's zero-coordinate samples. -/
theorem zeroOrbitSpectralSample_eq_on_orbit_of_eq_on_sampleFinset
    (ρ : ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      ∀ z : ℂ, z ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ z = zetaSpectralEval ψ z) :
    ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
      zetaSpectralEval φ η =
        zetaSpectralEval ψ η := by
  intro η hη
  exact hsample η hη

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

/-- Finite spectral localization for the completed zero tail.

This is the genuine localization input: preserve the prescribed finite spectral
samples while driving the complementary completed-zero tail below an arbitrary
positive tolerance. -/
theorem exists_autocorrelation_zeroTail_small_preserving_spectralSampleFinset_owner
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              z =
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
              z) ∧
          |Complex.re
            (zetaZeroTail S
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))| < ε := by
  intro ε hε
  match hZeroTailSmallValuesOwnerRunge S P f₀ hSeparated ε hε with
  | ⟨r, ⟨f, hfFiber, hr⟩, hrlt⟩ =>
      have htailValue :
          ZetaAdmissibleFunction.autocorrelationZeroTailRealAbs S f < ε :=
        Eq.subst (motive := fun value : ℝ => value < ε) hr hrlt
      exact ⟨f, hfFiber, htailValue⟩

omit hZeroTailSmallValuesOwnerRunge in
/-- Every completed-zero point in the orbit dagger window belongs to the
already dagger-closed orbit spectral sample set. -/
theorem mem_zetaZeroOrbitDaggerClosedSpectralSampleFinset_of_mem_completedWindow
    (rho eta : ℂ)
    (heta : eta ∈ zetaZeroOrbitDaggerClosedCompletedZeroFinset rho) :
    eta ∈ zetaZeroOrbitDaggerClosedSpectralSampleFinset rho := by
  have hdoubleClosure :
      eta ∈ ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
        (zetaZeroOrbitDaggerClosedSpectralSampleFinset rho) :=
    ZetaAdmissibleFunction.mem_daggerClosedSpectralSampleFinset_of_mem_completedZeroDaggerClosureFinset
      (zetaZeroOrbitDaggerClosedSpectralSampleFinset rho) eta heta
  have hidempotent :=
    ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset_idempotent
      (zetaZeroOrbitContributionSpectralSampleFinset rho)
  exact Eq.mp
    (congrArg (fun sampleSet : Finset ℂ => eta ∈ sampleSet) hidempotent)
    hdoubleClosure

/-- Finite zero-set localization preserves each zero spectral sample while making the
complementary zero-side tail arbitrarily small. -/
theorem exists_autocorrelation_zeroTail_small_preserving_finiteSpectralSamples_owner
    (S : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
                (zetaZeroTailSpectralSampleFinset S)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ η : ℂ, η ∈ S →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              η =
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
              η) ∧
          |Complex.re
            (zetaZeroTail S
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))| < ε := by
  intro ε hε
  match
    exists_autocorrelation_zeroTail_small_preserving_spectralSampleFinset_owner
      hZeroTailSmallValuesOwnerRunge
      S (zetaZeroTailSpectralSampleFinset S) f₀ hSeparated ε hε with
  | ⟨f, hsample, htail⟩ =>
    exact ⟨f,
      zeroTailSpectralSample_eq_on_zeroSet_of_eq_on_sampleFinset
        S
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
        hsample,
      htail⟩

/-- The dagger-closed completed-zero orbit window can be held at unit spectral
samples while its complementary tail is made arbitrarily small. -/
theorem exists_daggerClosedOrbit_autocorrelation_unitSamples_zeroTail_small
    (ρ : ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ η : ℂ,
          η ∈ zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ →
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f) η = 1) ∧
          |Complex.re
            (zetaZeroTail
              (zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ)
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))| < ε := by
  match exists_daggerClosedOrbit_autocorrelation_unitSpectralSamples ρ with
  | ⟨f₀, hf₀⟩ =>
      intro ε hε
      match
        exists_autocorrelation_zeroTail_small_preserving_spectralSampleFinset_owner
          hZeroTailSmallValuesOwnerRunge
          (zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ)
          (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ)
          f₀
          (zetaZeroOrbitDaggerClosedCompletedZeroFinset_rawSeparated ρ)
          ε hε with
      | ⟨f, hpreserved, htail⟩ =>
          have hwindow :
              ∀ η : ℂ,
                η ∈ zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ →
                  zetaSpectralEval
                    (ZetaAdmissibleFunction.convolutionAutocorrelation f) η = 1 := by
            intro η hη
            have hsample :
                η ∈ zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ :=
              mem_zetaZeroOrbitDaggerClosedSpectralSampleFinset_of_mem_completedWindow
                ρ η hη
            have hpreserved_eta := hpreserved η hsample
            exact Eq.trans hpreserved_eta (hf₀ η hsample)
          exact ⟨f, hwindow, htail⟩

omit hZeroTailSmallValuesOwnerRunge

/-- The real orbit remainder is the real part of the zero-tail outside the orbit. -/
theorem zetaZeroOrbitRemainderRe_eq_zeroTail_re
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainderRe ρ φ =
      Complex.re (zetaZeroTail (zetaZeroOrbitFinset ρ) φ) := by
  rfl

include hZeroTailSmallValuesOwnerRunge

/-- Localizing around a finite orbit preserves every individual orbit spectral sample while
making the complementary orbit tail arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitSpectralSamples_owner
    (ρ : ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ η : ℂ,
        ZetaCompletedZero η →
          η ∉ zetaZeroOrbitFinset ρ →
            η ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
                (zetaZeroOrbitFinset ρ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              η =
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
              η) ∧
          |zetaZeroOrbitRemainderRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε := by
  intro ε hε
  match
    exists_autocorrelation_zeroTail_small_preserving_spectralSampleFinset_owner
      hZeroTailSmallValuesOwnerRunge
      (zetaZeroOrbitFinset ρ) (zetaZeroOrbitFinset ρ) f₀
      hSeparated ε hε with
  | ⟨f, hsample, htail⟩ =>
    have hsample_orbit :
        ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              η =
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
              η :=
      zeroOrbitSpectralSample_eq_on_orbit_of_eq_on_sampleFinset
        ρ
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
        hsample
    have htail_orbit :
        |zetaZeroOrbitRemainderRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε := by
      exact Eq.subst
        (motive := fun x : ℝ => |x| < ε)
        (zetaZeroOrbitRemainderRe_eq_zeroTail_re
          ρ (ZetaAdmissibleFunction.convolutionAutocorrelation f)).symm
        htail
    exact ⟨f, hsample_orbit, htail_orbit⟩

/-- Localizing around a finite orbit preserves its autocorrelation contribution exactly while
making the complementary orbit tail arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitContribution_owner
    (ρ : ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ η : ℂ,
        ZetaCompletedZero η →
          η ∉ zetaZeroOrbitFinset ρ →
            η ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
                (zetaZeroOrbitFinset ρ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) ∧
          |zetaZeroOrbitRemainderRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)| < ε := by
  intro ε hε
  match
    exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitSpectralSamples_owner
      hZeroTailSmallValuesOwnerRunge
      ρ f₀ hSeparated ε hε with
  | ⟨f, hsample, htail⟩ =>
    have hcontribution :
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) :=
      zetaZeroOrbitContributionRe_eq_of_spectralEval_eq_on_orbit
        ρ
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
        hsample
    exact ⟨f, hcontribution, htail⟩

omit hZeroTailSmallValuesOwnerRunge

/-- Exact preservation of the finite orbit contribution transports a fixed negative
margin to the localized probe. -/
theorem zetaZeroOrbitContributionRe_le_margin_of_eq_reference
    (ρ : ℂ) (δ : ℝ)
    (f f₀ : ZetaAdmissibleFunction)
    (hcontribution :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀))
    (hmargin :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) ≤ -δ) :
    zetaZeroOrbitContributionRe ρ
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ := by
  calc
    zetaZeroOrbitContributionRe ρ
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) := by
      exact hcontribution
    _ ≤ -δ := by
      exact hmargin

include hZeroTailSmallValuesOwnerRunge

/-- Localizing around a finite-orbit negative-margin autocorrelation probe
preserves that margin and makes the orbit remainder arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_remainder_small_near_margin_probe_owner
    (ρ : ℂ)
    (δ : ℝ)
    (_hδ : 0 < δ)
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
  intro ε hε
  match
    exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitContribution_owner
      hZeroTailSmallValuesOwnerRunge
      ρ f₀ hSeparated ε hε with
  | ⟨f, hcontribution, htail⟩ =>
    have hmargin_f :
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ := by
      exact zetaZeroOrbitContributionRe_le_margin_of_eq_reference
        ρ δ f f₀ hcontribution hmargin
    exact ⟨f, hmargin_f, htail⟩

end

end LFunctions
end Boundary
