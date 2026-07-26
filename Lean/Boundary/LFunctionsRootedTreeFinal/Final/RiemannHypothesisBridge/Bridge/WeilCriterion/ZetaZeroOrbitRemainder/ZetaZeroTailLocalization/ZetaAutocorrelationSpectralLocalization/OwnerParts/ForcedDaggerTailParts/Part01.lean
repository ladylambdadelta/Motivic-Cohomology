import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CutoffData

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Correct forced-dagger finite-window selector from the non-dagger cutoff.

This is the proof body for the owner forced-dagger finite-window selector. -/
theorem autocorrelationSpectralEvalFiber_commonPolynomialEnvelope_forcedDaggerTailWindow_of_nonDaggerCutoff
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f)
                (zetaCenteredZero ρ) = 0) →
              autocorrelationZeroTailRealAbs S f < ε :=
  match
      exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported
        S P T₀ hT₀ ε hε A k hsum with
  | ⟨T, hT₀T, hT, htail⟩ =>
      ⟨T, hT₀T, hT,
        fun f hfFiber hfT =>
          autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
            S f ε
            (lt_of_le_of_lt
              (zetaZeroTail_norm_le_commonPolynomialEnvelope_nonDagger_complement_tsum
                S P T A k hA hsum f
                (zetaZeroSideContribution_eq_zero_of_window_spectralEval_zero
                  S T f hfT)
                (fun ρ hρDagger =>
                  hforced f hfFiber (ρ : ℂ) ρ.2.1 ρ.2.2.1 hρDagger)
                (fun ρ =>
                  henv f hfFiber
                    (autocorrelationSpectralEvalFiber_baseWindowVanishes_of_enlargedWindowVanishes
                      P T₀ T hT₀T f hfT)
                    (⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1,
                      fun hρT₀ => ρ.2.2.2.1 (hT₀T hρT₀)⟩ :
                      {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀})))
              htail)⟩

/-- Summable-tail selector with forced dagger-constrained zeros. -/
theorem autocorrelationSpectralEvalFiber_commonPolynomialEnvelope_forcedDaggerTailWindow_owner
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f)
                (zetaCenteredZero ρ) = 0) →
              autocorrelationZeroTailRealAbs S f < ε :=
  autocorrelationSpectralEvalFiber_commonPolynomialEnvelope_forcedDaggerTailWindow_of_nonDaggerCutoff
    S P f₀ ε hε T₀ hT₀ A k hA hsum hforced henv

/-- Finite-window tomography gives arbitrarily small attained zero-tail values.

This is the descent step from the true reconstruction engine to the metric value-set
form: once tomography supplies, for every tolerance, a finite zero window whose
annihilation controls the remaining zero tail, finite interpolation realizes that
annihilation window inside the fixed autocorrelation spectral fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_finiteWindowTailControl
    (hRunge : AutocorrelationSpectralEvalFiberFiniteWindowTailControlRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  fun ε hε =>
  match hRunge S P f₀ ε hε with
  | ⟨T, hT⟩ =>
      let hWindow :
          (∀ ρ : ℂ, ρ ∈ T →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
            ∀ f : ZetaAdmissibleFunction,
              f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
                (∀ ρ : ℂ, ρ ∈ T →
                  zetaSpectralEval (convolutionAutocorrelation f)
                    (zetaCenteredZero ρ) = 0) →
                  autocorrelationZeroTailRealAbs S f < ε :=
        autocorrelationSpectralEvalFiberFiniteWindowTailControl.elim
          S P f₀ ε T hT
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues_exists_lt_of_finiteWindow_tailControl
        S P f₀ ε T hWindow.1 hWindow.2

/-- Finite-window tomography gives the closure/radical form of the zero-tail value set.

This is the topological endpoint of the finite-window reconstruction chain.  It keeps the
only remaining analytic input at the correct owner level: proving the finite-window
tail-control theorem itself. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_finiteWindowTailControl
    (hRunge : AutocorrelationSpectralEvalFiberFiniteWindowTailControlRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure
      (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
    S P f₀
    (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_finiteWindowTailControl
      hRunge S P f₀)

/-- A common-polynomial finite-tail reconstruction package supplies finite-window
tail control.

This peels off the final projection from the analytic reconstruction theorem: its chosen
window `T` is already dagger-disjoint from the fixed autocorrelation constraints, and its
last field is exactly the tail-control predicate consumed by finite interpolation. -/
theorem autocorrelationSpectralEvalFiber_finiteWindowTailControl_of_commonPolynomialFiniteTail
    (hRunge : AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeFiniteTailRunge) :
    AutocorrelationSpectralEvalFiberFiniteWindowTailControlRunge :=
  fun S P f₀ ε hε =>
  match hRunge S P f₀ ε hε with
  | ⟨T₀, T, A, k, hT₀T, hT, hA, hsum, hforced, henv, htail⟩ =>
      ⟨T, hT, htail⟩

/-- A common-polynomial finite-tail reconstruction package gives the closure/radical
form of the fixed-fiber zero-tail value set.

The proof is deliberately only a composition of named owner steps: common-polynomial
finite-tail reconstruction gives finite-window tail control; finite-window tail control
gives small attained zero-tail values; small attained values give closure at `0`. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_commonPolynomialFiniteTail
    (hRunge : AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeFiniteTailRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure
      (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_finiteWindowTailControl
    (autocorrelationSpectralEvalFiber_finiteWindowTailControl_of_commonPolynomialFiniteTail
      hRunge)
    S P f₀

/-- Base common-polynomial reconstruction data supplies the finite-tail reconstruction
package.

This is the honest summable-tail selection step: the base theorem gives a dagger-disjoint
base window, forced vanishing of dagger-constrained completed zeros, and a common
polynomial envelope on the complementary zero-side terms; the non-dagger cutoff theorem
then selects the enlarged finite window whose annihilation forces the zero-tail below the
requested tolerance. -/
theorem autocorrelationSpectralEvalFiber_commonPolynomialFiniteTail_of_base
    (hbase : AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase) :
    AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeFiniteTailRunge :=
  fun S P f₀ ε hε =>
  match
      AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase.exists_data
        hbase S P f₀ with
  | ⟨T₀, A, k, hdata⟩ =>
      match
          autocorrelationSpectralEvalFiber_commonPolynomialEnvelope_forcedDaggerTailWindow_owner
            S P f₀ ε hε T₀
            (AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.baseWindow_disjoint
              hdata)
            A k
            (AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.constant_nonnegative
              hdata)
            (AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.envelope_summable
              hdata)
            (AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.forcedDagger_vanishes
              hdata)
            (AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.envelope_bound
              hdata) with
      | ⟨T, hT₀T, hT, htail⟩ =>
          ⟨T₀, T, A, k, hT₀T, hT,
            AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.constant_nonnegative
              hdata,
            AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.envelope_summable
              hdata,
            AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.forcedDagger_vanishes
              hdata,
            AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.envelope_bound
              hdata,
            htail⟩

/-- Base common-polynomial reconstruction data gives the closure/radical form of the
fixed-fiber zero-tail value set. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_commonPolynomialBase
    (hbase : AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure
      (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_commonPolynomialFiniteTail
    (autocorrelationSpectralEvalFiber_commonPolynomialFiniteTail_of_base hbase)
    S P f₀

/-- Owner separated finite-window tomographic reconstruction.

This is the remaining analytic root.  It selects only a finite dagger-disjoint window
after assuming the fixed finite spectral samples do not pin any completed-zero coordinate
in the complementary tail. -/
theorem autocorrelationSpectralEvalFiber_separatedFiniteWindowTailControl_of_separatedCommonPolynomialBase
    (hbase : AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase) :
    AutocorrelationSpectralEvalFiberSeparatedFiniteWindowTailControlRunge :=
  fun S P f₀ hSeparated ε hε =>
  match hbase S P f₀ hSeparated with
  | ⟨T₀, A, k, hdata⟩ =>
      match
          autocorrelationSpectralEvalFiber_polynomialEnvelopeFiniteTailControl
            S P f₀ ε hε T₀
            (AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.baseWindow_disjoint
              hdata)
            hSeparated
            A k
            (AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.constant_nonnegative
              hdata)
            (AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.envelope_summable
              hdata)
            (autocorrelationSpectralEvalFiber_forcedDaggerConstrainedZeroContribution_vanishes
              S P f₀ hSeparated)
            (AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.envelope_bound
              hdata) with
      | ⟨T, hT₀T, hT, htail⟩ =>
          ⟨T,
            autocorrelationSpectralEvalFiberFiniteWindowTailControl_intro
              S P f₀ ε T hT htail⟩

/-- Owner separated finite-window tomographic reconstruction. -/
theorem autocorrelationSpectralEvalFiber_separatedFiniteWindowTailControl_ownerTomographicReconstruction
    (hbase : AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase) :
    AutocorrelationSpectralEvalFiberSeparatedFiniteWindowTailControlRunge :=
  autocorrelationSpectralEvalFiber_separatedFiniteWindowTailControl_of_separatedCommonPolynomialBase
    hbase

/-- Separated finite-window tomography gives arbitrarily small attained zero-tail values. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_separatedFiniteWindowTailControl
    (hRunge : AutocorrelationSpectralEvalFiberSeparatedFiniteWindowTailControlRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  fun ε hε =>
  match hRunge S P f₀ hSeparated ε hε with
  | ⟨T, hT⟩ =>
      let hWindow :
          (∀ ρ : ℂ, ρ ∈ T →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
            ∀ f : ZetaAdmissibleFunction,
              f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
                (∀ ρ : ℂ, ρ ∈ T →
                  zetaSpectralEval (convolutionAutocorrelation f)
                    (zetaCenteredZero ρ) = 0) →
                  autocorrelationZeroTailRealAbs S f < ε :=
        autocorrelationSpectralEvalFiberFiniteWindowTailControl.elim
          S P f₀ ε T hT
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues_exists_lt_of_finiteWindow_tailControl
        S P f₀ ε T hWindow.1 hWindow.2

/-- Owner separated small-values Runge theorem. -/
theorem autocorrelationSpectralEvalFiberSeparatedZeroTailSmallValuesRunge_owner :
    AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase →
      AutocorrelationSpectralEvalFiberSeparatedZeroTailSmallValuesRunge :=
  fun hbase S P f₀ hSeparated =>
    autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_separatedFiniteWindowTailControl
      (autocorrelationSpectralEvalFiber_separatedFiniteWindowTailControl_ownerTomographicReconstruction
        hbase)
      S P f₀ hSeparated

/-- Quotient-level closure form transported from the concrete fixed-fiber closure form. -/
theorem autocorrelationSpectralFiberQuotientZeroTailClosureRunge_owner :
    AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase →
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      (∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) →
        (0 : ℝ) ∈ closure
          (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
            S P f₀) :=
  fun hbase S P f₀ hSeparated =>
  let hConcreteClosure :
      (0 : ℝ) ∈
        closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
    autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
      S P f₀
      (autocorrelationSpectralEvalFiberSeparatedZeroTailSmallValuesRunge_owner
        hbase S P f₀ hSeparated)
  let hConcrete_eq_quotient :
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ =
        autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀ :=
    Eq.trans
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq
        S P f₀).symm
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
        S P f₀)
  Eq.subst
    (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
    hConcrete_eq_quotient
    hConcreteClosure

theorem Real.dist_zero_eq_self_of_nonnegative
    (r : ℝ)
    (hr : 0 ≤ r) :
    dist 0 r = r :=
  Eq.trans
    (dist_comm 0 r)
    (Eq.trans
      (Real.dist_eq r 0)
      (Eq.trans
        (congrArg (fun x : ℝ => |x|) (sub_zero r))
        (abs_of_nonneg hr)))

/-- Quotient-level small-values form transported from quotient closure. -/
theorem autocorrelationSpectralFiberQuotientZeroTailSmallValuesRunge_owner :
    AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase →
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      (∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) →
        ∀ ε : ℝ, 0 < ε →
          ∃ r : ℝ,
            r ∈
              autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
                S P f₀ ∧
              r < ε :=
  fun hbase S P f₀ hSeparated ε hε =>
  match
      (Metric.mem_closure_iff.mp
        (autocorrelationSpectralFiberQuotientZeroTailClosureRunge_owner
          hbase S P f₀ hSeparated))
        ε hε with
  | ⟨r, hrValues, hdist⟩ =>
      let hrNonnegative :
          0 ≤ r :=
        autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues_nonnegative
          S P f₀ hrValues
      let hdist_zero_r_eq_r : dist 0 r = r :=
        Real.dist_zero_eq_self_of_nonnegative r hrNonnegative
      ⟨r, hrValues,
        Eq.subst
          (motive := fun x : ℝ => x < ε)
          hdist_zero_r_eq_r
          hdist⟩

end ZetaAdmissibleFunction
end LFunctions
end Boundary
