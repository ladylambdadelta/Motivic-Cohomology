import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.EnvelopeBase

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The completed-zero complement after removing a second finite window is the
set-theoretic complement of that window inside the first zero tail. -/
def zetaZeroTailWindowComplementEquiv
    (S : Finset ℂ)
    (T : Finset ℂ) :
    {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S ∧ rho ∉ T} ≃
      ((fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
        (rho : ℂ) ∈ T)ᶜ : Set {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S}) where
  toFun := fun rho =>
    ⟨⟨(rho : ℂ), rho.2.1, rho.2.2.1⟩, rho.2.2.2⟩
  invFun := fun rho =>
    ⟨(rho : ℂ), rho.1.2.1, rho.1.2.2, rho.2⟩
  left_inv := fun rho => Subtype.ext (Eq.refl (rho : ℂ))
  right_inv := fun rho =>
    Subtype.ext (Subtype.ext (Eq.refl ((rho : {rho : ℂ //
      ZetaCompletedZero rho ∧ rho ∉ S}) : ℂ)))

/-- A summable envelope on all completed zeros remains summable after an
injective completed-zero parametrization. -/
theorem zetaCompletedZeroPolynomialEnvelope_comp_summable
    {index : Type}
    (A : ℝ)
    (k : ℕ)
    (zeroMap : index → {rho : ℂ // ZetaCompletedZero rho})
    (zeroMapInjective : Function.Injective zeroMap)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          A * zetaCompletedZeroCenteredHeight rho ^ (-(k + 3 : ℤ)))) :
    Summable
      (fun element : index =>
        A * zetaCompletedZeroCenteredHeight (zeroMap element) ^
          (-(k + 3 : ℤ))) := by
  exact hsum.comp_injective zeroMapInjective

theorem zetaZeroTail_eq_complement_tsum_of_zero_on_window_partition
    (S : Finset ℂ)
    (T : Finset ℂ)
    (φ : ZetaAdmissibleFunction)
    (hsummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          zetaZeroSideContribution (ρ : ℂ) φ))
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) φ = 0) :
    zetaZeroTail S φ =
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) φ := by
  let α := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}
  let β := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T}
  let contribution : α → ℂ :=
    fun ρ => zetaZeroSideContribution (ρ : ℂ) φ
  let killed : Set α := fun ρ => (ρ : ℂ) ∈ T
  let complementEquiv : β ≃ (killedᶜ : Set α) :=
    zetaZeroTailWindowComplementEquiv S T
  have hsplit :
      (∑' ρ : killed, contribution ρ) +
          (∑' ρ : (killedᶜ : Set α), contribution ρ) =
        ∑' ρ : α, contribution ρ :=
    tsum_subtype_add_tsum_subtype_compl hsummable killed
  have hkilled_fun :
      (fun ρ : killed => contribution ρ) = fun rho : killed => 0 :=
    funext (fun rho => hzeroT (rho : α) rho.2)
  have hkilled_tsum :
      (∑' ρ : killed, contribution ρ) = 0 :=
    Eq.trans
      (congrArg
        (fun f : killed → ℂ => ∑' ρ : killed, f ρ)
        hkilled_fun)
      tsum_zero
  have htail_unfold :
      zetaZeroTail S φ = ∑' ρ : α, contribution ρ :=
    Eq.refl (zetaZeroTail S φ)
  have hright_transport :
      (∑' ρ : (killedᶜ : Set α), contribution ρ) =
        ∑' ρ : β, zetaZeroSideContribution (ρ : ℂ) φ :=
    have hraw :
        (∑' ρ : (killedᶜ : Set α), contribution ρ) =
          ∑' ρ : β, contribution (complementEquiv ρ) :=
      ((complementEquiv).tsum_eq
        (fun ρ : (killedᶜ : Set α) => contribution ρ)).symm
    have hterm :
        (fun ρ : β => contribution (complementEquiv ρ)) =
          fun ρ : β => zetaZeroSideContribution (ρ : ℂ) φ :=
      funext (fun rho => Eq.refl (zetaZeroSideContribution (rho : ℂ) φ))
    Eq.trans hraw
      (congrArg (fun F : β → ℂ => ∑' ρ : β, F ρ) hterm)
  have htotal_eq_right :
      (∑' ρ : α, contribution ρ) =
        ∑' ρ : β, zetaZeroSideContribution (ρ : ℂ) φ :=
    Eq.trans
      hsplit.symm
      (Eq.trans
        (congrArg
          (fun z : ℂ =>
            z + (∑' ρ : (killedᶜ : Set α), contribution ρ))
          hkilled_tsum)
        (Eq.trans
          (zero_add (∑' ρ : (killedᶜ : Set α), contribution ρ))
          hright_transport))
  exact Eq.trans htail_unfold htotal_eq_right

/-- Public zero-window removal theorem. -/
theorem zetaZeroTail_eq_complement_tsum_of_zero_on_window_ownerGap
    (S : Finset ℂ)
    (T : Finset ℂ)
    (φ : ZetaAdmissibleFunction)
    (hsummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          zetaZeroSideContribution (ρ : ℂ) φ))
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) φ = 0) :
    zetaZeroTail S φ =
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) φ := by
  exact
    zetaZeroTail_eq_complement_tsum_of_zero_on_window_partition
      S T φ hsummable hzeroT

/-- The norm of a complementary completed-zero `tsum` is bounded by a summable
nonnegative polynomial envelope. -/
theorem zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_by_majorization
    (S : Finset ℂ)
    (T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (f : ZetaAdmissibleFunction)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f))‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  let envelope :
      {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T} → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let contribution :
      {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T} → ℂ :=
    fun ρ =>
      zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)
  let zeroMap :
      {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T} →
        {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun rho => ⟨(rho : ℂ), rho.2.1⟩
  have zeroMapInjective : Function.Injective zeroMap :=
    fun left right equality =>
      Subtype.ext
        (congrArg
          (fun zero : {ρ : ℂ // ZetaCompletedZero ρ} => (zero : ℂ))
          equality)
  have henvelope_summable : Summable envelope :=
    zetaCompletedZeroPolynomialEnvelope_comp_summable
      A k zeroMap zeroMapInjective hsum
  have hnorm_summable : Summable (fun ρ => ‖contribution ρ‖) := by
    have hnorm_bound : ∀ ρ, ‖‖contribution ρ‖‖ ≤ envelope ρ :=
      fun rho =>
        (Eq.subst
          (motive := fun value : ℝ => value ≤ envelope rho)
          (norm_norm (contribution rho)).symm
          (hbound rho))
    exact Summable.of_norm_bounded envelope henvelope_summable hnorm_bound
  have hnorm_tsum :
      ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          contribution ρ)‖ ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          ‖contribution ρ‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have hmajorant_tsum :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          ‖contribution ρ‖) ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          envelope ρ :=
    tsum_le_tsum hbound hnorm_summable henvelope_summable
  exact hnorm_tsum.trans hmajorant_tsum

/-- Public complementary polynomial-envelope norm estimate. -/
theorem zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_tsum_ownerGap
    (S : Finset ℂ)
    (T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (f : ZetaAdmissibleFunction)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f))‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  exact
    zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_by_majorization
      S T A k hsum f hbound

/-- The norm of a complementary completed-zero `tsum` is bounded by the
non-dagger part of a summable polynomial envelope when dagger-constrained
terms vanish.

This is the corrected norm estimate for the forced-dagger tail selector: the
dagger-constrained complement contributes zero by `hforcedZero`, so the only
positive majorant mass charged to the tail is over zeros whose centered sample
is outside the dagger-closed finite spectral constraint set. -/
theorem zetaZeroTail_norm_le_commonPolynomialEnvelope_nonDagger_by_partition
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
    (f : ZetaAdmissibleFunction)
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hforcedZero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hboundNonDagger :
      ∀ ρ :
        {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖zetaZeroTail S (convolutionAutocorrelation f)‖ ≤
      ∑' ρ :
        {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  have htail_eq :
      zetaZeroTail S (convolutionAutocorrelation f) =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) :=
    let envelope :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℝ :=
      fun ρ =>
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
    let contribution :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ :=
      fun ρ =>
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)
    let zeroMap :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} →
          {ρ : ℂ // ZetaCompletedZero ρ} :=
      fun rho => ⟨(rho : ℂ), rho.2.1⟩
    have zeroMapInjective : Function.Injective zeroMap :=
      fun left right equality =>
        Subtype.ext
          (congrArg
            (fun zero : {ρ : ℂ // ZetaCompletedZero ρ} => (zero : ℂ))
            equality)
    have henvelope_summable : Summable envelope :=
      zetaCompletedZeroPolynomialEnvelope_comp_summable
        A k zeroMap zeroMapInjective hsum
    have hnorm_bound :
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          ‖contribution ρ‖ ≤ envelope ρ :=
      fun ρ =>
            match (inferInstance : Decidable ((ρ : ℂ) ∈ T)) with
            | isTrue hρT =>
                have hcontribution_zero : contribution ρ = 0 :=
                  hzeroT ρ hρT
                have hnorm_zero : ‖contribution ρ‖ = 0 :=
                  Eq.trans (congrArg norm hcontribution_zero) norm_zero
                have henvelope_nonneg : 0 ≤ envelope ρ :=
                  zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
                    (⟨(ρ : ℂ), ρ.2.1⟩ :
                      {ρ : ℂ // ZetaCompletedZero ρ})
                Eq.subst
                  (motive := fun value : ℝ => value ≤ envelope ρ)
                  hnorm_zero.symm
                  henvelope_nonneg
            | isFalse hρT =>
                match (inferInstance :
                    Decidable
                      (zetaCenteredZero (ρ : ℂ) ∈
                        daggerClosedSpectralSampleFinset P)) with
                | isTrue hρDagger =>
                    have hcontribution_zero : contribution ρ = 0 :=
                      hforcedZero
                        (⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT⟩ :
                          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T})
                        hρDagger
                    have hnorm_zero : ‖contribution ρ‖ = 0 :=
                      Eq.trans (congrArg norm hcontribution_zero) norm_zero
                    have henvelope_nonneg : 0 ≤ envelope ρ :=
                      zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
                        (⟨(ρ : ℂ), ρ.2.1⟩ :
                          {ρ : ℂ // ZetaCompletedZero ρ})
                    Eq.subst
                      (motive := fun value : ℝ => value ≤ envelope ρ)
                      hnorm_zero.symm
                      henvelope_nonneg
                | isFalse hρNonDagger =>
                    hboundNonDagger
                      (⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT, hρNonDagger⟩ :
                        {ρ : ℂ //
                          ZetaCompletedZero ρ ∧
                            ρ ∉ S ∧
                            ρ ∉ T ∧
                            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P})
    have htail_contribution_summable : Summable contribution :=
      Summable.of_norm_bounded envelope henvelope_summable hnorm_bound
    zetaZeroTail_eq_complement_tsum_of_zero_on_window_ownerGap
      S T (convolutionAutocorrelation f) htail_contribution_summable hzeroT
  have hcomplement_bound :
      ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f))‖ ≤
        ∑' ρ :
          {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ T ∧
              zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
    zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_nonDagger_tsum
      S P T A k hA hsum (convolutionAutocorrelation f)
        hforcedZero hboundNonDagger
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ∑' ρ :
            {ρ : ℂ //
              ZetaCompletedZero ρ ∧
                ρ ∉ S ∧
                ρ ∉ T ∧
                zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
      htail_eq.symm
      hcomplement_bound

/-- Public non-dagger complementary polynomial-envelope estimate. -/
theorem zetaZeroTail_norm_le_commonPolynomialEnvelope_nonDagger_complement_tsum
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
    (f : ZetaAdmissibleFunction)
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hforcedZero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hboundNonDagger :
      ∀ ρ :
        {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖zetaZeroTail S (convolutionAutocorrelation f)‖ ≤
      ∑' ρ :
        {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  exact
    zetaZeroTail_norm_le_commonPolynomialEnvelope_nonDagger_by_partition
      S P T A k hA hsum f hzeroT hforcedZero hboundNonDagger

/-- The remaining summable-tail cutoff for a common completed-zero polynomial envelope.

This is the finite-excision estimate behind the common-envelope norm estimate: after
the killed finite window is removed, the remaining complementary `tsum` is bounded by
the complementary polynomial-envelope tail. -/
theorem zetaZeroTail_norm_le_commonPolynomialEnvelope_complement_by_partition
    (S : Finset ℂ)
    (T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (f : ZetaAdmissibleFunction)
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖zetaZeroTail S (convolutionAutocorrelation f)‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  have htail_eq :
      zetaZeroTail S (convolutionAutocorrelation f) =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) :=
    let envelope :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℝ :=
      fun ρ =>
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
    let contribution :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ :=
      fun ρ =>
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)
    let zeroMap :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} →
          {ρ : ℂ // ZetaCompletedZero ρ} :=
      fun rho => ⟨(rho : ℂ), rho.2.1⟩
    have zeroMapInjective : Function.Injective zeroMap :=
      fun left right equality =>
        Subtype.ext
          (congrArg
            (fun zero : {ρ : ℂ // ZetaCompletedZero ρ} => (zero : ℂ))
            equality)
    have henvelope_summable : Summable envelope :=
      zetaCompletedZeroPolynomialEnvelope_comp_summable
        A k zeroMap zeroMapInjective hsum
    have hnorm_bound :
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          ‖contribution ρ‖ ≤ envelope ρ :=
      fun ρ =>
        match (inferInstance : Decidable ((ρ : ℂ) ∈ T)) with
            | isTrue hρT =>
                have hcontribution_zero : contribution ρ = 0 :=
                  hzeroT ρ hρT
                have hnorm_zero : ‖contribution ρ‖ = 0 :=
                  Eq.trans (congrArg norm hcontribution_zero) norm_zero
                have henvelope_nonneg : 0 ≤ envelope ρ :=
                  zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
                    (⟨(ρ : ℂ), ρ.2.1⟩ :
                      {ρ : ℂ // ZetaCompletedZero ρ})
                Eq.subst
                  (motive := fun value : ℝ => value ≤ envelope ρ)
                  hnorm_zero.symm
                  henvelope_nonneg
            | isFalse hρT =>
                hbound
                  (⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T})
    have htail_contribution_summable : Summable contribution :=
      Summable.of_norm_bounded envelope henvelope_summable hnorm_bound
    zetaZeroTail_eq_complement_tsum_of_zero_on_window_ownerGap
      S T (convolutionAutocorrelation f) htail_contribution_summable hzeroT
  have hcomplement_bound :
      ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f))‖ ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
    zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_tsum_ownerGap
      S T A k hsum f hbound
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
      htail_eq.symm
      hcomplement_bound

/-- Public common polynomial-envelope complementary-tail estimate. -/
theorem zetaZeroTail_norm_le_commonPolynomialEnvelope_complement_tsum_ownerGap
    (S : Finset ℂ)
    (T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (f : ZetaAdmissibleFunction)
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖zetaZeroTail S (convolutionAutocorrelation f)‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  exact
    zetaZeroTail_norm_le_commonPolynomialEnvelope_complement_by_partition
      S T A k hA hsum f hzeroT hbound

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
