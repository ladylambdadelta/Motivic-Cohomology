import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.Prelude
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.TailPartition

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_nonDagger_tsum
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (φ : ZetaAdmissibleFunction)
    (hforcedZero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
          zetaZeroSideContribution (ρ : ℂ) φ = 0)
    (hboundNonDagger :
      ∀ ρ :
        {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        ‖zetaZeroSideContribution (ρ : ℂ) φ‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) φ)‖ ≤
      ∑' ρ :
        {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
  let γ := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T}
  let δ :=
    {ρ : ℂ //
      ZetaCompletedZero ρ ∧
        ρ ∉ S ∧
        ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P}
  let contribution : γ → ℂ :=
    fun ρ => zetaZeroSideContribution (ρ : ℂ) φ
  let envelopeγ : γ → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let envelopeδ : δ → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let nonDagger : Set γ :=
    fun ρ => zetaCenteredZero (ρ : ℂ) ∉ daggerClosedSpectralSampleFinset P
  let completedZeroMapγ : γ → {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun ρ => ⟨(ρ : ℂ), ρ.2.1⟩
  have hcompletedZeroMapγ_injective : Function.Injective completedZeroMapγ :=
    fun left right heq =>
      Subtype.ext
        (congrArg
          (fun zero : {ρ : ℂ // ZetaCompletedZero ρ} => (zero : ℂ))
          heq)
  have henvelopeγ_composed_summable :
      Summable
        ((fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∘
            completedZeroMapγ) :=
    hsum.comp_injective hcompletedZeroMapγ_injective
  have henvelopeγ_composed_eq :
      ((fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∘
          completedZeroMapγ) =
        (fun ρ : γ =>
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :=
    Eq.refl
      (fun ρ : γ =>
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
  have henvelopeγ_restricted_summable :
      Summable
        (fun ρ : γ =>
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :=
    Eq.subst
      (motive := fun sequence : γ → ℝ => Summable sequence)
      henvelopeγ_composed_eq
      henvelopeγ_composed_summable
  have henvelopeγ_eq :
      (fun ρ : γ =>
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
        envelopeγ :=
    Eq.refl envelopeγ
  have henvelopeγ_summable : Summable envelopeγ :=
    Eq.subst
      (motive := fun sequence : γ → ℝ => Summable sequence)
      henvelopeγ_eq
      henvelopeγ_restricted_summable
  let hnorm_bound : ∀ ρ : γ, ‖‖contribution ρ‖‖ ≤ envelopeγ ρ :=
    fun ρ =>
      match (inferInstance :
          Decidable (zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P)) with
      | isTrue hρDagger =>
          let hzero : contribution ρ = 0 :=
            hforcedZero ρ hρDagger
          let hnorm_zero_raw : ‖contribution ρ‖ = ‖(0 : ℂ)‖ :=
            congrArg norm hzero
          let hnorm_zero : ‖contribution ρ‖ = 0 :=
            Eq.trans hnorm_zero_raw norm_zero
          let henv_nonneg : 0 ≤ envelopeγ ρ :=
            zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ})
          let hnormNorm :
              ‖‖contribution ρ‖‖ = ‖contribution ρ‖ :=
            norm_norm (contribution ρ)
          le_trans (le_of_eq hnormNorm)
            (le_trans (le_of_eq hnorm_zero) henv_nonneg)
      | isFalse hρNonDagger =>
          let hnormNorm :
              ‖‖contribution ρ‖‖ = ‖contribution ρ‖ :=
            norm_norm (contribution ρ)
          let hbound : ‖contribution ρ‖ ≤ envelopeγ ρ :=
            hboundNonDagger
              (⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1, ρ.2.2.2, hρNonDagger⟩ : δ)
          le_trans (le_of_eq hnormNorm) hbound
  let hnorm_summable : Summable (fun ρ : γ => ‖contribution ρ‖) :=
    Summable.of_norm_bounded envelopeγ henvelopeγ_summable hnorm_bound
  have hnorm_tsum :
      ‖(∑' ρ : γ, contribution ρ)‖ ≤
        ∑' ρ : γ, ‖contribution ρ‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  let toNonDagger : δ → nonDagger :=
    fun ρ =>
      ⟨⟨(ρ : ℂ),
          And.intro ρ.2.1
            (And.intro ρ.2.2.1 ρ.2.2.2.1)⟩,
        ρ.2.2.2.2⟩
  let fromNonDagger : nonDagger → δ :=
    fun ρ =>
      ⟨(ρ.val : γ),
        And.intro ρ.1.2.1
          (And.intro ρ.1.2.2.1
            (And.intro ρ.1.2.2.2 ρ.2))⟩
  have htoFrom : Function.LeftInverse fromNonDagger toNonDagger :=
    fun ρ => Subtype.ext (Eq.refl ρ.val)
  have hfromTo : Function.RightInverse fromNonDagger toNonDagger :=
    fun ρ => Subtype.ext (Eq.refl ρ.val)
  let nonDaggerEquiv : δ ≃ nonDagger :=
    Equiv.mk toNonDagger fromNonDagger htoFrom hfromTo
  have hsplit :
      (∑' ρ : nonDagger, ‖contribution ρ‖) +
          (∑' ρ : (nonDaggerᶜ : Set γ), ‖contribution ρ‖) =
        ∑' ρ : γ, ‖contribution ρ‖ :=
    tsum_subtype_add_tsum_subtype_compl hnorm_summable nonDagger
  have hdagger_zero_pointwise :
      ∀ ρ : (nonDaggerᶜ : Set γ), ‖contribution ρ‖ = 0 :=
    fun ρ =>
      let hρDagger :
          zetaCenteredZero ((ρ : γ) : ℂ) ∈ daggerClosedSpectralSampleFinset P :=
        match (inferInstance :
            Decidable
              (zetaCenteredZero ((ρ : γ) : ℂ) ∈
                daggerClosedSpectralSampleFinset P)) with
        | isTrue hρDagger =>
            hρDagger
        | isFalse hρNonDagger =>
            False.elim (ρ.2 hρNonDagger)
      let hzero : contribution (ρ : γ) = 0 :=
        hforcedZero (ρ : γ) hρDagger
      let hnormZeroRaw : ‖contribution (ρ : γ)‖ = ‖(0 : ℂ)‖ :=
        congrArg norm hzero
      Eq.trans hnormZeroRaw norm_zero
  have hdagger_zero_fun :
      (fun ρ : (nonDaggerᶜ : Set γ) => ‖contribution ρ‖) =
        fun zeroElement : (nonDaggerᶜ : Set γ) => 0 :=
    funext hdagger_zero_pointwise
  have hdagger_zero_tsum :
      (∑' ρ : (nonDaggerᶜ : Set γ), ‖contribution ρ‖) = 0 :=
    Eq.trans
      (congrArg
        (fun F : (nonDaggerᶜ : Set γ) → ℝ =>
          ∑' ρ : (nonDaggerᶜ : Set γ), F ρ)
        hdagger_zero_fun)
      tsum_zero
  have hnondagger_transport :
      (∑' ρ : nonDagger, ‖contribution ρ‖) =
        ∑' ρ : δ, ‖contribution (nonDaggerEquiv ρ : γ)‖ :=
    ((nonDaggerEquiv).tsum_eq
      (fun ρ : nonDagger => ‖contribution ρ‖)).symm
  let hnondagger_bound :
      (∑' ρ : δ, ‖contribution (nonDaggerEquiv ρ : γ)‖) ≤
        ∑' ρ : δ, envelopeδ ρ :=
    let completedZeroMapδ : δ → {ρ : ℂ // ZetaCompletedZero ρ} :=
      fun ρ => ⟨(ρ : ℂ), ρ.2.1⟩
    have hcompletedZeroMapδ_injective : Function.Injective completedZeroMapδ :=
      fun left right heq =>
        Subtype.ext
          (congrArg
            (fun zero : {ρ : ℂ // ZetaCompletedZero ρ} => (zero : ℂ))
            heq)
    have henvelopeδ_composed_summable :
        Summable
          ((fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∘
              completedZeroMapδ) :=
      hsum.comp_injective hcompletedZeroMapδ_injective
    have henvelopeδ_composed_eq :
        ((fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∘
            completedZeroMapδ) =
          (fun ρ : δ =>
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :=
      Eq.refl
        (fun ρ : δ =>
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    have henvelopeδ_restricted_summable :
        Summable
          (fun ρ : δ =>
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :=
      Eq.subst
        (motive := fun sequence : δ → ℝ => Summable sequence)
        henvelopeδ_composed_eq
        henvelopeδ_composed_summable
    have henvelopeδ_eq :
        (fun ρ : δ =>
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
          envelopeδ :=
      Eq.refl envelopeδ
    have henvelopeδ_summable : Summable envelopeδ :=
      Eq.subst
        (motive := fun sequence : δ → ℝ => Summable sequence)
        henvelopeδ_eq
        henvelopeδ_restricted_summable
    let hnormδ_bound :
        ∀ ρ : δ,
          ‖‖contribution (nonDaggerEquiv ρ : γ)‖‖ ≤ envelopeδ ρ :=
      fun ρ =>
        let hnormNorm :
            ‖‖contribution (nonDaggerEquiv ρ : γ)‖‖ =
              ‖contribution (nonDaggerEquiv ρ : γ)‖ :=
          norm_norm (contribution (nonDaggerEquiv ρ : γ))
        le_trans (le_of_eq hnormNorm) (hboundNonDagger ρ)
    let hnormδ_summable :
        Summable (fun ρ : δ => ‖contribution (nonDaggerEquiv ρ : γ)‖) :=
      Summable.of_norm_bounded envelopeδ henvelopeδ_summable
        hnormδ_bound
    tsum_le_tsum
      (fun ρ => hboundNonDagger ρ)
      hnormδ_summable
      henvelopeδ_summable
  let hnorm_sum_le_nondagger :
      (∑' ρ : γ, ‖contribution ρ‖) ≤
        ∑' ρ : δ, envelopeδ ρ :=
    let hsum_eq_nondagger :
        (∑' ρ : γ, ‖contribution ρ‖) =
          ∑' ρ : nonDagger, ‖contribution ρ‖ :=
      Eq.trans
        hsplit.symm
        (Eq.trans
          (congrArg
            (fun x : ℝ => (∑' ρ : nonDagger, ‖contribution ρ‖) + x)
            hdagger_zero_tsum)
          (add_zero (∑' ρ : nonDagger, ‖contribution ρ‖)))
    Eq.subst
      (motive := fun x : ℝ => x ≤ ∑' ρ : δ, envelopeδ ρ)
      hsum_eq_nondagger.symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ∑' ρ : δ, envelopeδ ρ)
        hnondagger_transport.symm
        hnondagger_bound)
  le_trans hnorm_tsum hnorm_sum_le_nondagger

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
