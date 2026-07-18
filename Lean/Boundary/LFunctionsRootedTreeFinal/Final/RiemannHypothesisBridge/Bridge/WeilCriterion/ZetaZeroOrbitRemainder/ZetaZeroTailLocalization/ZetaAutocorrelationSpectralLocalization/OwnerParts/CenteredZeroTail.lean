import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleExponentialModulation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.NonDaggerComplement
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CenteredCoordinates

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem zetaCenteredZeroSideContribution_def
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaCenteredZeroSideContribution ρ φ =
      - (zetaZeroMultiplicity ρ : ℂ) *
        zetaSpectralEval φ (zetaCenteredZero ρ) := by
  exact Eq.refl _

theorem zetaCenteredZeroSideContribution_eq_shiftedRawContribution
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaCenteredZeroSideContribution ρ φ =
      zetaZeroSideContribution ρ
        (exponentialModulate (-(1 / 2 : ℝ)) φ) := by
  have heval :
      zetaSpectralEval (exponentialModulate (-(1 / 2 : ℝ)) φ) ρ =
        zetaSpectralEval φ (zetaCenteredZero ρ) := by
    exact zetaSpectralEval_inverseModulation_at_zero φ ρ
  calc
    zetaCenteredZeroSideContribution ρ φ =
        - (zetaZeroMultiplicity ρ : ℂ) *
          zetaSpectralEval φ (zetaCenteredZero ρ) := by
      exact zetaCenteredZeroSideContribution_def ρ φ
    _ = - (zetaZeroMultiplicity ρ : ℂ) *
          zetaSpectralEval (exponentialModulate (-(1 / 2 : ℝ)) φ) ρ := by
      exact congrArg
        (fun z : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * z)
        heval.symm
    _ = zetaZeroSideContribution ρ
          (exponentialModulate (-(1 / 2 : ℝ)) φ) := by
      exact (zetaZeroSideContribution_def ρ
        (exponentialModulate (-(1 / 2 : ℝ)) φ)).symm

theorem zetaCenteredZeroTail_eq_shiftedRawTail
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaCenteredZeroTail S φ =
      zetaZeroTail S (exponentialModulate (-(1 / 2 : ℝ)) φ) := by
  exact tsum_congr (fun ρ =>
    zetaCenteredZeroSideContribution_eq_shiftedRawContribution
      (ρ : ℂ) φ)

theorem zetaCenteredZeroTail_eq_rawTail_of_shiftedConvolution
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    zetaCenteredZeroTail S (convolutionAutocorrelation f) =
      zetaZeroTail S
        (convolutionAutocorrelationShifted (-(1 / 2 : ℝ)) f) := by
  have hconvolution :
      convolutionAutocorrelationShifted (-(1 / 2 : ℝ)) f =
        exponentialModulate (-(1 / 2 : ℝ))
          (convolutionAutocorrelation f) := by
    exact convolutionAutocorrelationShifted_eq_exponentialModulate
      (-(1 / 2 : ℝ)) f
  have htail := zetaCenteredZeroTail_eq_shiftedRawTail
    S (convolutionAutocorrelation f)
  exact Eq.trans htail
    (congrArg (fun φ : ZetaAdmissibleFunction => zetaZeroTail S φ)
      hconvolution.symm)

theorem zetaZeroTail_eq_centeredTail_of_positiveModulation
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    zetaZeroTail S (convolutionAutocorrelation f) =
      zetaCenteredZeroTail S
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) := by
  have hshifted := zetaCenteredZeroTail_eq_shiftedRawTail
    S (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
  have hplus :=
    convolutionAutocorrelationShifted_eq_exponentialModulate
      (1 / 2 : ℝ) f
  have hcomp := exponentialModulate_comp
    (-(1 / 2 : ℝ)) (1 / 2 : ℝ) (convolutionAutocorrelation f)
  have hzero := exponentialModulate_zero (convolutionAutocorrelation f)
  have hcancel : -(1 / 2 : ℝ) + (1 / 2 : ℝ) = 0 := by
    exact neg_add_cancel (1 / 2 : ℝ)
  have hconvolution :
      exponentialModulate (-(1 / 2 : ℝ))
          (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) =
        convolutionAutocorrelation f := by
    calc
      exponentialModulate (-(1 / 2 : ℝ))
          (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) =
          exponentialModulate (-(1 / 2 : ℝ))
            (exponentialModulate (1 / 2 : ℝ)
              (convolutionAutocorrelation f)) := by
        exact congrArg
          (fun φ : ZetaAdmissibleFunction =>
            exponentialModulate (-(1 / 2 : ℝ)) φ)
          hplus
      _ = exponentialModulate
            (-(1 / 2 : ℝ) + (1 / 2 : ℝ))
              (convolutionAutocorrelation f) := hcomp
      _ = exponentialModulate 0 (convolutionAutocorrelation f) := by
        exact congrArg
          (fun c : ℝ => exponentialModulate c
            (convolutionAutocorrelation f)) hcancel
      _ = convolutionAutocorrelation f := hzero
  have hraw :
      zetaCenteredZeroTail S
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) =
        zetaZeroTail S (convolutionAutocorrelation f) := by
    exact Eq.trans hshifted
      (congrArg (fun φ : ZetaAdmissibleFunction => zetaZeroTail S φ)
        hconvolution)
  exact hraw.symm

theorem autocorrelationZeroTailRealAbs_lt_of_positiveModulation_centeredNorm_lt
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) (ε : ℝ)
    (hcentered :
      ‖zetaCenteredZeroTail S
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ < ε) :
    autocorrelationZeroTailRealAbs S f < ε := by
  have htail := zetaZeroTail_eq_centeredTail_of_positiveModulation S f
  have hnorm : ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε := by
    exact Eq.subst (motive := fun z : ℂ => ‖z‖ < ε) htail.symm hcentered
  exact autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
    S f ε hnorm

theorem zetaCenteredZeroSideContribution_positiveModulation_eq_raw
    (ρ : ℂ) (f : ZetaAdmissibleFunction) :
    zetaCenteredZeroSideContribution ρ
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) =
      zetaZeroSideContribution ρ (convolutionAutocorrelation f) := by
  have heval :=
    zetaSpectralEval_positiveModulation_at_centeredZero f ρ
  calc
    zetaCenteredZeroSideContribution ρ
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) =
        - (zetaZeroMultiplicity ρ : ℂ) *
          zetaSpectralEval
            (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
            (zetaCenteredZero ρ) :=
      zetaCenteredZeroSideContribution_def ρ
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
    _ = - (zetaZeroMultiplicity ρ : ℂ) *
          zetaSpectralEval (convolutionAutocorrelation f) ρ := by
      exact congrArg
        (fun z : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * z) heval
    _ = zetaZeroSideContribution ρ
        (convolutionAutocorrelation f) := by
      exact (zetaZeroSideContribution_def ρ
        (convolutionAutocorrelation f)).symm

theorem zetaCenteredZeroSideContribution_positiveModulation_eq_zero_of_raw_spectralEval_zero
    (ρ : ℂ) (f : ZetaAdmissibleFunction)
    (hρ : zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) :
    zetaCenteredZeroSideContribution ρ
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0 := by
  have hraw := zetaCenteredZeroSideContribution_positiveModulation_eq_raw ρ f
  have hzero : zetaZeroSideContribution ρ
      (convolutionAutocorrelation f) = 0 := by
    calc
      zetaZeroSideContribution ρ (convolutionAutocorrelation f) =
          - (zetaZeroMultiplicity ρ : ℂ) *
            zetaSpectralEval (convolutionAutocorrelation f) ρ :=
        zetaZeroSideContribution_def ρ (convolutionAutocorrelation f)
      _ = - (zetaZeroMultiplicity ρ : ℂ) * 0 :=
        congrArg
          (fun z : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * z) hρ
      _ = 0 := mul_zero _
  exact Eq.trans hraw hzero

theorem zetaCenteredZeroSideContribution_positiveModulation_eq_zero_of_raw_zero
    (ρ : ℂ) (f : ZetaAdmissibleFunction)
    (hzero : zetaZeroSideContribution ρ
      (convolutionAutocorrelation f) = 0) :
    zetaCenteredZeroSideContribution ρ
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0 := by
  exact Eq.trans
    (zetaCenteredZeroSideContribution_positiveModulation_eq_raw ρ f)
    hzero

theorem zetaCenteredZeroSideContribution_positiveModulation_norm_le_of_raw_norm_le
    (ρ : ℂ) (f : ZetaAdmissibleFunction) (B : ℝ)
    (hbound : ‖zetaZeroSideContribution ρ
      (convolutionAutocorrelation f)‖ ≤ B) :
    ‖zetaCenteredZeroSideContribution ρ
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤ B := by
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ B)
    (zetaCenteredZeroSideContribution_positiveModulation_eq_raw ρ f).symm
    hbound

theorem zetaCenteredZeroSideContribution_eq_inverseModulation_raw
    (ρ : ℂ) (f : ZetaAdmissibleFunction) :
    zetaCenteredZeroSideContribution ρ
        (convolutionAutocorrelation f) =
      zetaZeroSideContribution ρ
        (convolutionAutocorrelationShifted (-(1 / 2 : ℝ)) f) := by
  have hshift :=
    zetaCenteredZeroSideContribution_eq_shiftedRawContribution
      ρ (convolutionAutocorrelation f)
  have hconv :=
    convolutionAutocorrelationShifted_eq_exponentialModulate
      (-(1 / 2 : ℝ)) f
  calc
    zetaCenteredZeroSideContribution ρ
        (convolutionAutocorrelation f) =
        zetaZeroSideContribution ρ
          (exponentialModulate (-(1 / 2 : ℝ))
            (convolutionAutocorrelation f)) := hshift
    _ = zetaZeroSideContribution ρ
          (convolutionAutocorrelationShifted (-(1 / 2 : ℝ)) f) := by
      exact congrArg
        (fun φ : ZetaAdmissibleFunction => zetaZeroSideContribution ρ φ)
        hconv.symm

theorem zetaCenteredZeroTail_complement_norm_le_nonDagger_tsum
    (S P T : Finset ℂ) (A : ℝ) (k : ℕ) (hA : 0 ≤ A)
    (hsum : Summable (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (f : ZetaAdmissibleFunction)
    (hforcedZero : ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
      zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
        zetaCenteredZeroSideContribution (ρ : ℂ)
          f = 0)
    (hboundNonDagger : ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
      ‖zetaCenteredZeroSideContribution (ρ : ℂ) f‖ ≤
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ))) :
    ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZeroSideContribution (ρ : ℂ) f)‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)) := by
  let g : ZetaAdmissibleFunction := exponentialModulate (-(1 / 2 : ℝ)) f
  have hcontribution : ∀ ρ : ℂ,
      zetaCenteredZeroSideContribution ρ f =
        zetaZeroSideContribution ρ g := by
    intro ρ
    have hshift := zetaCenteredZeroSideContribution_eq_shiftedRawContribution
      ρ f
    exact Eq.trans hshift rfl
  have hforcedRaw : ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
      zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
        zetaZeroSideContribution (ρ : ℂ)
          g = 0 := by
    intro ρ hρ
    exact Eq.trans (hcontribution (ρ : ℂ)).symm (hforcedZero ρ hρ)
  have hboundRaw : ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          ‖zetaZeroSideContribution (ρ : ℂ) g‖ ≤
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)) := by
    intro ρ
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)))
      (hcontribution (ρ : ℂ)) (hboundNonDagger ρ)
  have hraw :=
    zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_nonDagger_tsum
      S P T A k hA hsum g hforcedRaw hboundRaw
  have hsumEq :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZeroSideContribution (ρ : ℂ)
          f) =
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) g := by
    exact tsum_congr (fun ρ => hcontribution (ρ : ℂ))
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)))
    hsumEq.symm hraw

theorem zetaCenteredZeroTail_def
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaCenteredZeroTail S φ =
      tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
        zetaCenteredZeroSideContribution (η : ℂ) φ) := by
  exact Eq.refl _

theorem zetaCenteredZeroSideContribution_eq_zero_of_spectralEval_zero
    (φ : ZetaAdmissibleFunction)
    (ρ : ℂ)
    (hρ : zetaSpectralEval φ (zetaCenteredZero ρ) = 0) :
    zetaCenteredZeroSideContribution ρ φ = 0 := by
  have hscaled :
      - (zetaZeroMultiplicity ρ : ℂ) *
          zetaSpectralEval φ (zetaCenteredZero ρ) =
        - (zetaZeroMultiplicity ρ : ℂ) * 0 :=
    congrArg
      (fun z : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * z)
      hρ
  exact
    Eq.trans
      (zetaCenteredZeroSideContribution_def ρ φ)
      (Eq.trans hscaled (mul_zero (- (zetaZeroMultiplicity ρ : ℂ))))

theorem zetaCenteredZeroSideContribution_eq_zero_of_window_spectralEval_zero
    (S : Finset ℂ)
    (T : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval f
          (zetaCenteredZero ρ) = 0) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
      (ρ : ℂ) ∈ T →
        zetaCenteredZeroSideContribution (ρ : ℂ)
          f = 0 := by
  intro ρ hρT
  exact
    zetaCenteredZeroSideContribution_eq_zero_of_spectralEval_zero
      f (ρ : ℂ)
      (hfT (ρ : ℂ) hρT)

theorem zetaCenteredZeroSpectralEval_baseWindowVanishes_of_enlargedWindowVanishes
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (f : ZetaAdmissibleFunction)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0) :
    ∀ ρ : ℂ, ρ ∈ T₀ →
      zetaSpectralEval (convolutionAutocorrelation f)
        (zetaCenteredZero ρ) = 0 := by
  intro ρ hρT₀
  exact hfT ρ (hT₀T hρT₀)

def zetaCenteredZeroTailWindowComplementEquiv
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

theorem zetaCenteredZeroTail_eq_complement_tsum_of_zero_on_window
    (S : Finset ℂ)
    (T : Finset ℂ)
    (φ : ZetaAdmissibleFunction)
    (hsummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          zetaCenteredZeroSideContribution (ρ : ℂ) φ))
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0) :
    zetaCenteredZeroTail S φ =
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZeroSideContribution (ρ : ℂ) φ := by
  let α := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}
  let β := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T}
  let contribution : α → ℂ :=
    fun ρ => zetaCenteredZeroSideContribution (ρ : ℂ) φ
  let killed : Set α := fun ρ => (ρ : ℂ) ∈ T
  let complementEquiv : β ≃ (killedᶜ : Set α) :=
    zetaCenteredZeroTailWindowComplementEquiv S T
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
      zetaCenteredZeroTail S φ = ∑' ρ : α, contribution ρ :=
    Eq.refl (zetaCenteredZeroTail S φ)
  have hright_transport :
      (∑' ρ : (killedᶜ : Set α), contribution ρ) =
        ∑' ρ : β, zetaCenteredZeroSideContribution (ρ : ℂ) φ :=
    have hraw :
        (∑' ρ : (killedᶜ : Set α), contribution ρ) =
          ∑' ρ : β, contribution (complementEquiv ρ) :=
      ((complementEquiv).tsum_eq
        (fun ρ : (killedᶜ : Set α) => contribution ρ)).symm
    have hterm :
        (fun ρ : β => contribution (complementEquiv ρ)) =
          fun ρ : β => zetaCenteredZeroSideContribution (ρ : ℂ) φ :=
      funext (fun rho => Eq.refl (zetaCenteredZeroSideContribution (rho : ℂ) φ))
    Eq.trans hraw
      (congrArg (fun F : β → ℂ => ∑' ρ : β, F ρ) hterm)
  have htotal_eq_right :
      (∑' ρ : α, contribution ρ) =
        ∑' ρ : β, zetaCenteredZeroSideContribution (ρ : ℂ) φ :=
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

theorem zetaCenteredZeroTail_complement_tsum_norm_le_envelope
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
        ‖zetaCenteredZeroSideContribution (ρ : ℂ)
            (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZeroSideContribution (ρ : ℂ)
          (convolutionAutocorrelation f))‖ ≤
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
      zetaCenteredZeroSideContribution (ρ : ℂ)
        (convolutionAutocorrelation f)
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
    hsum.comp_injective zeroMapInjective
  have hnorm_summable : Summable (fun ρ => ‖contribution ρ‖) := by
    have hnorm_bound : ∀ ρ, ‖‖contribution ρ‖‖ ≤ envelope ρ :=
      fun rho =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ envelope rho)
          (norm_norm (contribution rho)).symm
          (hbound rho)
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

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
