import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.PresentationParts.Part01_ValueDefinitions
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CenteredZeroTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CutoffData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CenteredCoordinates

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The dagger constraints of a raw sample fiber, expressed in centered coordinates. -/
def centeredDaggerClosedSpectralSampleFinset
    (P : Finset ℂ) (c : ℝ) : Finset ℂ :=
  translatedSpectralSampleFinset (daggerClosedSpectralSampleFinset P) c

/-- The centered coordinate of a raw zero is its raw coordinate minus one half. -/
theorem zetaCenteredZero_eq_sub_half
    (ρ : ℂ) :
    zetaCenteredZero ρ = ρ - (1 / 2 : ℂ) :=
  Eq.refl (zetaCenteredZero ρ)

/-- Translating a centered coordinate back by one half recovers the raw coordinate. -/
theorem zetaCenteredZero_add_half
    (ρ : ℂ) :
    zetaCenteredZero ρ + (1 / 2 : ℂ) = ρ :=
  Eq.trans
    (congrArg (fun z : ℂ => z + (1 / 2 : ℂ))
      (zetaCenteredZero_eq_sub_half ρ))
    (sub_add_cancel ρ (1 / 2 : ℂ))

/-- If two centered coordinates agree after the one-half translation, then the
raw zero coordinates agree. -/
theorem raw_eq_of_centered_eq_translated_half
    (ρ z : ℂ)
    (hcentered : zetaCenteredZero ρ = z - (1 / 2 : ℂ)) :
    ρ = z :=
  Eq.trans
    (zetaCenteredZero_add_half ρ).symm
    (Eq.trans
      (congrArg (fun value : ℂ => value + (1 / 2 : ℂ)) hcentered)
      (sub_add_cancel z (1 / 2 : ℂ)))

/-- Membership in the centered dagger-closed sample gives a raw dagger-closed
sample after adding back one half. -/
theorem raw_mem_daggerClosed_of_centeredDaggerClosed
    (P : Finset ℂ)
    (ρ : ℂ)
    (hcentered :
      zetaCenteredZero ρ ∈
        centeredDaggerClosedSpectralSampleFinset P (1 / 2 : ℝ)) :
    ρ ∈ daggerClosedSpectralSampleFinset P :=
  match Finset.mem_image.mp hcentered with
  | ⟨z, hz, hzeq⟩ =>
      let hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) :=
        Complex.ofReal_div 1 2
      let hcenteredEq : zetaCenteredZero ρ = z - (1 / 2 : ℂ) :=
        Eq.trans hzeq.symm
          (congrArg (fun value : ℂ => z - value) hhalf)
      let hrawEq : ρ = z :=
        raw_eq_of_centered_eq_translated_half ρ z hcenteredEq
      Eq.subst hrawEq.symm hz

/-- Raw dagger separation gives the corresponding centered-coordinate separation. -/
theorem centeredZero_not_mem_centeredDaggerClosed_of_not_mem_daggerClosed
    (P : Finset ℂ)
    (ρ : ℂ)
    (hρ : ρ ∉ daggerClosedSpectralSampleFinset P) :
    zetaCenteredZero ρ ∉
      centeredDaggerClosedSpectralSampleFinset P (1 / 2 : ℝ) :=
  fun hcentered =>
    hρ (raw_mem_daggerClosed_of_centeredDaggerClosed P ρ hcentered)

/-- Membership in the twice-translated sample reduces to membership in the
original sample. -/
theorem mem_of_mem_translatedSpectralSampleFinset_comp
    (P : Finset ℂ)
    (c : ℝ)
    (z : ℂ)
    (hz : z ∈ translatedSpectralSampleFinset
        (translatedSpectralSampleFinset P c) (-c)) :
    z ∈ P :=
  match Finset.mem_image.mp hz with
  | ⟨y, hy, hzy⟩ =>
      match Finset.mem_image.mp hy with
      | ⟨w, hw, hwy⟩ =>
          let hyz : y + (c : ℂ) = z :=
            Eq.trans
              (Eq.trans
                (sub_neg_eq_add y (c : ℂ)).symm
                (congrArg (fun value : ℂ => y - value)
                  (Complex.ofReal_neg c).symm))
              hzy
          let hwy_add : (w - (c : ℂ)) + (c : ℂ) = y + (c : ℂ) :=
            congrArg (fun value : ℂ => value + (c : ℂ)) hwy
          let hwz : w = z :=
            Eq.trans
              (Eq.trans (sub_add_cancel w (c : ℂ)).symm hwy_add)
              hyz
          Eq.subst hwz hw

/-- Membership in the original sample lifts to the twice-translated sample. -/
theorem mem_translatedSpectralSampleFinset_comp_of_mem
    (P : Finset ℂ)
    (c : ℝ)
    (z : ℂ)
    (hz : z ∈ P) :
    z ∈ translatedSpectralSampleFinset
        (translatedSpectralSampleFinset P c) (-c) :=
  let hmem : z - (c : ℂ) ∈ translatedSpectralSampleFinset P c :=
    Finset.mem_image.mpr
      ⟨z, hz, Eq.refl (z - (c : ℂ))⟩
  let hsum : (z - (c : ℂ)) + (c : ℂ) = z :=
    sub_add_cancel z (c : ℂ)
  Finset.mem_image.mpr
    ⟨z - (c : ℂ), hmem,
      Eq.trans
        (congrArg (fun value : ℂ => (z - (c : ℂ)) - value)
          (Complex.ofReal_neg c))
        (Eq.trans (sub_neg_eq_add (z - (c : ℂ)) (c : ℂ)) hsum)⟩

theorem translatedSpectralSampleFinset_comp
    (P : Finset ℂ) (c : ℝ) :
    translatedSpectralSampleFinset
        (translatedSpectralSampleFinset P c) (-c) = P :=
  Finset.ext
    (fun z =>
      Iff.intro
        (fun hz => mem_of_mem_translatedSpectralSampleFinset_comp P c z hz)
        (fun hz => mem_translatedSpectralSampleFinset_comp_of_mem P c z hz))

/-- A shifted fiber evaluation unfolds to the raw fiber evaluation at the
translated argument. -/
theorem shifted_convolution_spectralEval_eq_raw_add
    (c : ℝ)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaSpectralEval
        (convolutionAutocorrelationShifted c f) z =
      zetaSpectralEval (convolutionAutocorrelation f) (z + (c : ℂ)) :=
  Eq.trans
    (congrArg (fun g : ZetaAdmissibleFunction =>
      zetaSpectralEval g z)
      (convolutionAutocorrelationShifted_eq_exponentialModulate c f))
    (zetaSpectralEval_exponentialModulate c
      (convolutionAutocorrelation f) z)

/-- A raw fiber evaluation is the shifted fiber evaluation at the translated-back
argument. -/
theorem raw_spectralEval_eq_shifted_sub
    (c : ℝ)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaSpectralEval (convolutionAutocorrelation f) z =
      zetaSpectralEval (convolutionAutocorrelationShifted c f)
        (z - (c : ℂ)) :=
  let harg : (z - (c : ℂ)) + (c : ℂ) = z :=
    sub_add_cancel z (c : ℂ)
  Eq.trans
    (congrArg
      (fun q : ℂ => zetaSpectralEval
        (convolutionAutocorrelation f) q)
      harg.symm)
    (Eq.trans
      (zetaSpectralEval_exponentialModulate c
        (convolutionAutocorrelation f) (z - (c : ℂ))).symm
      (congrArg
        (fun q : ZetaAdmissibleFunction => zetaSpectralEval q
          (z - (c : ℂ)))
        (convolutionAutocorrelationShifted_eq_exponentialModulate c f).symm))

theorem mem_autocorrelationSpectralEvalFiberOf_translatedModulation
    (P : Finset ℂ)
    (c : ℝ)
    (f₀ f : ZetaAdmissibleFunction)
    (hf : f ∈ AutocorrelationSpectralEvalFiberOf P f₀) :
    f ∈ AutocorrelationSpectralEvalFiberOfShifted
        (translatedSpectralSampleFinset P c)
        c f₀ :=
  fun z hz =>
    match Finset.mem_image.mp hz with
    | ⟨w, hwP, hzw⟩ =>
        let hz_formula : z + (c : ℂ) = w :=
          Eq.trans
            (congrArg (fun value : ℂ => value + (c : ℂ)) hzw.symm)
            (sub_add_cancel w (c : ℂ))
        Eq.trans
          (shifted_convolution_spectralEval_eq_raw_add c f z)
          (Eq.trans
            (hf (z + (c : ℂ)) (Eq.subst hz_formula.symm hwP))
            (shifted_convolution_spectralEval_eq_raw_add c f₀ z).symm)

theorem mem_autocorrelationSpectralEvalFiberOf_inverseTranslatedModulation
    (P : Finset ℂ)
    (c : ℝ)
    (f₀ g : ZetaAdmissibleFunction)
    (hg : g ∈ AutocorrelationSpectralEvalFiberOfShifted
        (translatedSpectralSampleFinset P c)
        c f₀) :
    g ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
  fun z hz =>
    let hzTranslated : z - (c : ℂ) ∈
        translatedSpectralSampleFinset P c :=
      Finset.mem_image.mpr
        ⟨z, hz, Eq.refl (z - (c : ℂ))⟩
    Eq.trans
      (raw_spectralEval_eq_shifted_sub c g z)
      (Eq.trans
        (hg (z - (c : ℂ)) hzTranslated)
        (raw_spectralEval_eq_shifted_sub c f₀ z).symm)

theorem centered_tail_window_selector_of_nonDagger_cutoff
    (S : Finset ℂ)
    (P : Finset ℂ)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ : {ρ : ℂ //
          ZetaCompletedZero ρ ∧
            ρ ∉ S ∧
            ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε :=
  match
      exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported
        S P T₀ hT₀ ε hε A k hsum with
  | ⟨T, hT₀T, hT, htail⟩ =>
      ⟨T, hT₀T, hT, htail⟩

theorem centered_window_zero_contribution_of_centered_window_vanishing
    (S T : Finset ℂ)
    (φ : ZetaAdmissibleFunction)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval φ
          (zetaCenteredZero ρ) = 0) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
      (ρ : ℂ) ∈ T →
        zetaCenteredZeroSideContribution (ρ : ℂ)
          φ = 0 :=
  zetaCenteredZeroSideContribution_eq_zero_of_window_spectralEval_zero
    S T φ hfT

/-- Forced vanishing on dagger-constrained zeros and an envelope on the complementary
zeros give one envelope bound on the entire finite-window complement. -/
theorem centered_zero_side_contribution_bound_of_forced_and_nonDagger
    (S P T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (φ : ZetaAdmissibleFunction)
    (hforced :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
          zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ))) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
      ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ ≤
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)) :=
  fun ρ =>
  match (inferInstance : Decidable
      (zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P)) with
  | isTrue hρDagger =>
      let hzero : zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0 :=
        hforced ρ hρDagger
      let hnormZero : ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ = 0 :=
        Eq.trans (congrArg norm hzero) norm_zero
      let henvNonnegative :
          0 ≤ A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)) :=
        zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ})
      le_trans (le_of_eq hnormZero) henvNonnegative
  | isFalse hρDagger =>
      hbound
        ⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1, ρ.2.2.2, hρDagger⟩

theorem centered_zero_side_contribution_norm_summable_of_window_vanishing
    (S T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (φ : ZetaAdmissibleFunction)
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaCenteredZeroSideContribution (ρ : ℂ)
            φ = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaCenteredZeroSideContribution (ρ : ℂ)
            φ‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
        ‖zetaCenteredZeroSideContribution (ρ : ℂ)
          φ‖) :=
  let α := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}
  let contribution : α → ℂ :=
    fun ρ => zetaCenteredZeroSideContribution (ρ : ℂ)
      φ
  let envelope : α → ℝ :=
    fun ρ => A * zetaCompletedZeroCenteredHeight
      (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let zeroMap : α → {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun ρ => ⟨(ρ : ℂ), ρ.2.1⟩
  let hzeroMap : Function.Injective zeroMap :=
    fun left right heq =>
      Subtype.ext
        (congrArg (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (ρ : ℂ)) heq)
  let henvelope : Summable envelope :=
    let hcomposed : Summable ((fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∘ zeroMap) :=
      hsum.comp_injective hzeroMap
    let hcomposed_eq :
        ((fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∘ zeroMap) =
          envelope :=
      funext (fun ρ => Eq.refl (envelope ρ))
    Eq.subst
      (motive := fun sequence : α → ℝ => Summable sequence)
      hcomposed_eq
      hcomposed
  let hnormBound : ∀ ρ : α, ‖‖contribution ρ‖‖ ≤ envelope ρ :=
    fun ρ =>
    match (inferInstance : Decidable ((ρ : ℂ) ∈ T)) with
    | isTrue hρT =>
        let hzero : contribution ρ = 0 := hzeroT ρ hρT
        let hnormZero : ‖contribution ρ‖ = 0 :=
          Eq.trans (congrArg norm hzero) norm_zero
        let henvNonnegative : 0 ≤ envelope ρ :=
          zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ})
        le_trans
          (le_of_eq (norm_norm (contribution ρ)))
          (le_trans (le_of_eq hnormZero) henvNonnegative)
    | isFalse hρT =>
        let hboundρ : ‖contribution ρ‖ ≤ envelope ρ :=
          hbound ⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT⟩
        le_trans (le_of_eq (norm_norm (contribution ρ))) hboundρ
  Summable.of_norm_bounded envelope henvelope hnormBound

/-- The centered tail norm is bounded by the non-dagger envelope outside the
selected finite window. -/
theorem centered_tail_norm_le_nonDagger_envelope_of_centered_window_vanishing
    (S P T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (φ : ZetaAdmissibleFunction)
    (hforced :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
          zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)))
    (hwindow :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval φ (zetaCenteredZero ρ) = 0) :
    ‖zetaCenteredZeroTail S φ‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)) :=
  let hwindowZero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0 :=
    centered_window_zero_contribution_of_centered_window_vanishing
      S T φ hwindow
  let hgeneralBound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)) :=
    centered_zero_side_contribution_bound_of_forced_and_nonDagger
      S P T A k hA φ hforced hbound
  let hnormSummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖) :=
    centered_zero_side_contribution_norm_summable_of_window_vanishing
      S T A k hA hsum φ hwindowZero hgeneralBound
  let hcontributionSummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          zetaCenteredZeroSideContribution (ρ : ℂ) φ) :=
    Summable.of_norm hnormSummable
  let htailEq :
      zetaCenteredZeroTail S φ =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaCenteredZeroSideContribution (ρ : ℂ) φ :=
    zetaCenteredZeroTail_eq_complement_tsum_of_zero_on_window
      S T φ hcontributionSummable hwindowZero
  let hnormEq :
      ‖zetaCenteredZeroTail S φ‖ =
        ‖∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ :=
    congrArg norm htailEq
  let htailBound :
      ‖∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)) :=
    zetaCenteredZeroTail_complement_norm_le_nonDagger_tsum
      S P T A k hA hsum φ hforced hbound
  le_trans
    (le_of_eq hnormEq)
    htailBound

/-- A centered finite window, dagger-selected vanishing, and the complementary
envelope bound control the entire centered tail. -/
theorem centered_tail_bound_of_centered_window_vanishing
    (S P T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (ε : ℝ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (htail :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ))) < ε)
    (φ : ZetaAdmissibleFunction)
    (hforced :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
          zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
        ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)))
    (hwindow :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval φ (zetaCenteredZero ρ) = 0) :
    ‖zetaCenteredZeroTail S φ‖ < ε :=
  lt_of_le_of_lt
    (centered_tail_norm_le_nonDagger_envelope_of_centered_window_vanishing
      S P T A k hA hsum φ hforced hbound hwindow)
    htail

theorem centered_tail_coordinate_transport_owner
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
    (hpositiveForced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOfShifted
          (translatedSpectralSampleFinset P (1 / 2 : ℝ))
          (1 / 2 : ℝ) f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaCenteredZeroSideContribution ρ
                    (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0)
    (hpositiveEnv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOfShifted
          (translatedSpectralSampleFinset P (1 / 2 : ℝ))
          (1 / 2 : ℝ) f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
              (zetaCenteredZero ρ) = 0) →
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
            ‖zetaCenteredZeroSideContribution (ρ : ℂ)
                (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
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
              zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) →
              autocorrelationZeroTailRealAbs S f < ε :=
  match
      centered_tail_window_selector_of_nonDagger_cutoff
        S P ε hε T₀ hT₀ A k hsum with
  | ⟨T, hT₀T, hT, htail⟩ =>
      ⟨T, hT₀T, hT,
        fun f hfFiber hfWindow =>
          let hfshiftedFiber :
              f ∈ AutocorrelationSpectralEvalFiberOfShifted
                (translatedSpectralSampleFinset P (1 / 2 : ℝ))
                (1 / 2 : ℝ) f₀ :=
            mem_autocorrelationSpectralEvalFiberOf_translatedModulation
              P (1 / 2 : ℝ) f₀ f hfFiber
          let hfplusWindow :
              ∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval
                    (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
                    (zetaCenteredZero ρ) = 0 :=
            fun ρ hρ =>
              Eq.trans
                (zetaSpectralEval_positiveModulation_at_centeredZero f ρ)
                (hfWindow ρ hρ)
          let hplusForced :
              ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
                  zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
                  zetaCenteredZeroSideContribution (ρ : ℂ)
                    (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0 :=
            fun ρ hρ =>
              hpositiveForced f hfshiftedFiber
                (ρ : ℂ) ρ.2.1 ρ.2.2.1 hρ
          let hplusBound :
              ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
                zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
                ‖zetaCenteredZeroSideContribution (ρ : ℂ)
                    (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
                  A * zetaCompletedZeroCenteredHeight
                    (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                      (-(k + 3 : ℤ)) :=
            fun ρ =>
              let hρT₀ : (ρ : ℂ) ∉ T₀ :=
                fun hρT₀ => ρ.2.2.2.1 (hT₀T hρT₀)
              hpositiveEnv f hfshiftedFiber
                (fun σ hσT₀ => hfplusWindow σ (hT₀T hσT₀))
                ⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1, hρT₀⟩
          let hplusLt :
              ‖zetaCenteredZeroTail S
                  (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ < ε :=
            centered_tail_bound_of_centered_window_vanishing
              S P T A k ε hA hsum htail
              (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
              hplusForced hplusBound hfplusWindow
          autocorrelationZeroTailRealAbs_lt_of_positiveModulation_centeredNorm_lt
            S f ε hplusLt⟩

/-- The direct centered-coordinate tail selector.  `ZetaCompletedZero` already
uses centered coordinates, so finite windows and dagger constraints are evaluated at
the completed-zero coordinate itself. -/
theorem autocorrelationSpectralEvalFiber_directCenteredTailWindow
    (S P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ : ∀ ρ : ℂ, ρ ∈ T₀ →
      ρ ∉ daggerClosedSpectralSampleFinset P)
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
          ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
            ρ ∈ daggerClosedSpectralSampleFinset P →
              zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) →
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
            ‖zetaZeroSideContribution (ρ : ℂ)
                (convolutionAutocorrelation f)‖ ≤
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                  (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) →
              autocorrelationZeroTailRealAbs S f < ε :=
  match
      exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported
        S P T₀ hT₀ ε hε A k hsum with
  | ⟨T, hT₀T, hT, htail⟩ =>
      ⟨T, hT₀T, hT,
        fun f hfFiber hfT =>
          let hzeroWindow :
              ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
                (ρ : ℂ) ∈ T →
                  zetaZeroSideContribution (ρ : ℂ)
                    (convolutionAutocorrelation f) = 0 :=
            zetaZeroSideContribution_eq_zero_of_window_spectralEval_zero
              S T f hfT
          let hforcedWindow :
              ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
                (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution (ρ : ℂ)
                    (convolutionAutocorrelation f) = 0 :=
            fun ρ hρDagger =>
              hforced f hfFiber (ρ : ℂ) ρ.2.1 ρ.2.2.1 hρDagger
          let hbaseWindow :
              ∀ ρ : ℂ, ρ ∈ T₀ →
                zetaSpectralEval (convolutionAutocorrelation f) ρ = 0 :=
            autocorrelationSpectralEvalFiber_baseWindowVanishes_of_enlargedWindowVanishes
              P T₀ T hT₀T f hfT
          let henvWindow :
              ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
                ρ ∉ daggerClosedSpectralSampleFinset P},
                ‖zetaZeroSideContribution (ρ : ℂ)
                    (convolutionAutocorrelation f)‖ ≤
                  A * zetaCompletedZeroCenteredHeight
                    (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                      (-(k + 3 : ℤ)) :=
            fun ρ =>
              henv f hfFiber hbaseWindow
                (⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1,
                  fun hρT₀ => ρ.2.2.2.1 (hT₀T hρT₀)⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀})
          let htailNorm :
              ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε :=
            lt_of_le_of_lt
              (zetaZeroTail_norm_le_commonPolynomialEnvelope_nonDagger_complement_tsum
                S P T A k hA hsum f hzeroWindow hforcedWindow henvWindow)
              htail
          autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
            S f ε htailNorm⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
