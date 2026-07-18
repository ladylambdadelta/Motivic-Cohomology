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

/-- Raw dagger separation gives the corresponding centered-coordinate separation. -/
theorem centeredZero_not_mem_centeredDaggerClosed_of_not_mem_daggerClosed
    (P : Finset ℂ)
    (ρ : ℂ)
    (hρ : ρ ∉ daggerClosedSpectralSampleFinset P) :
    zetaCenteredZero ρ ∉
      centeredDaggerClosedSpectralSampleFinset P (1 / 2 : ℝ) := by
  intro hcentered
  obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hcentered
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) :=
    Complex.ofReal_div 1 2
  have hcentered_def : zetaCenteredZero ρ = ρ - (1 / 2 : ℂ) :=
    Eq.refl (zetaCenteredZero ρ)
  have hcenteredEq : zetaCenteredZero ρ = z - (1 / 2 : ℂ) := by
    calc
      zetaCenteredZero ρ = ρ - (1 / 2 : ℂ) := hcentered_def
      _ = zetaCenteredZero ρ := hcentered_def.symm
      _ = z - ((1 / 2 : ℝ) : ℂ) := hzeq.symm
      _ = z - (1 / 2 : ℂ) :=
        congrArg (fun value : ℂ => z - value) hhalf
  have hrawEq : ρ = z := by
    calc
      ρ = zetaCenteredZero ρ + (1 / 2 : ℂ) := by
        exact (sub_add_cancel ρ (1 / 2 : ℂ)).symm
      _ = (z - (1 / 2 : ℂ)) + (1 / 2 : ℂ) := by
        exact congrArg (fun value : ℂ => value + (1 / 2 : ℂ)) hcenteredEq
      _ = z := sub_add_cancel z (1 / 2 : ℂ)
  exact hρ (Eq.subst hrawEq.symm hz)


theorem translatedSpectralSampleFinset_comp
    (P : Finset ℂ) (c : ℝ) :
    translatedSpectralSampleFinset
        (translatedSpectralSampleFinset P c) (-c) = P := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := Finset.mem_image.mp hz
    obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hy
    have hyz : y + (c : ℂ) = z := by
      exact Eq.trans
        (Eq.trans
          (sub_neg_eq_add y (c : ℂ)).symm
          (congrArg (fun value : ℂ => y - value) (Complex.ofReal_neg c).symm))
        hzy
    have hwy_add : (w - (c : ℂ)) + (c : ℂ) = y + (c : ℂ) := by
      exact congrArg (fun value : ℂ => value + (c : ℂ)) hwy
    have hwz : w = z := by
      exact Eq.trans
        (Eq.trans (sub_add_cancel w (c : ℂ)).symm hwy_add)
        hyz
    exact Eq.subst hwz hw
  · intro hz
    have hmem : z - (c : ℂ) ∈ translatedSpectralSampleFinset P c := by
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hsum : (z - (c : ℂ)) + (c : ℂ) = z :=
      sub_add_cancel z (c : ℂ)
    exact Finset.mem_image.mpr
      ⟨z - (c : ℂ), hmem,
        Eq.trans
          (congrArg (fun value : ℂ => (z - (c : ℂ)) - value)
            (Complex.ofReal_neg c))
          (Eq.trans (sub_neg_eq_add (z - (c : ℂ)) (c : ℂ)) hsum)⟩

theorem mem_autocorrelationSpectralEvalFiberOf_translatedModulation
    (P : Finset ℂ)
    (c : ℝ)
    (f₀ f : ZetaAdmissibleFunction)
    (hf : f ∈ AutocorrelationSpectralEvalFiberOf P f₀) :
    f ∈ AutocorrelationSpectralEvalFiberOfShifted
        (translatedSpectralSampleFinset P c)
        c f₀ := by
  intro z hz
  obtain ⟨w, hwP, hzw⟩ := Finset.mem_image.mp hz
  have hz_formula : z + (c : ℂ) = w := by
    exact Eq.trans
      (congrArg (fun value : ℂ => value + (c : ℂ)) hzw.symm)
      (sub_add_cancel w (c : ℂ))
  have hleft :
      zetaSpectralEval
        (convolutionAutocorrelationShifted c f) z =
        zetaSpectralEval (convolutionAutocorrelation f) (z + (c : ℂ)) := by
    exact Eq.trans
      (congrArg (fun g : ZetaAdmissibleFunction =>
        zetaSpectralEval g z)
        (convolutionAutocorrelationShifted_eq_exponentialModulate c f))
      (zetaSpectralEval_exponentialModulate c
        (convolutionAutocorrelation f) z)
  have hright :
      zetaSpectralEval
        (convolutionAutocorrelationShifted c f₀) z =
        zetaSpectralEval (convolutionAutocorrelation f₀) (z + (c : ℂ)) := by
    exact Eq.trans
      (congrArg (fun g : ZetaAdmissibleFunction =>
        zetaSpectralEval g z)
        (convolutionAutocorrelationShifted_eq_exponentialModulate c f₀))
      (zetaSpectralEval_exponentialModulate c
        (convolutionAutocorrelation f₀) z)
  calc
    zetaSpectralEval
        (convolutionAutocorrelationShifted c f) z =
        zetaSpectralEval (convolutionAutocorrelation f) (z + (c : ℂ)) := hleft
    _ = zetaSpectralEval (convolutionAutocorrelation f₀) (z + (c : ℂ)) := by
      exact hf (z + (c : ℂ)) (Eq.subst hz_formula.symm hwP)
    _ = zetaSpectralEval
        (convolutionAutocorrelationShifted c f₀) z := hright.symm

theorem mem_autocorrelationSpectralEvalFiberOf_inverseTranslatedModulation
    (P : Finset ℂ)
    (c : ℝ)
    (f₀ g : ZetaAdmissibleFunction)
    (hg : g ∈ AutocorrelationSpectralEvalFiberOfShifted
        (translatedSpectralSampleFinset P c)
        c f₀) :
    g ∈ AutocorrelationSpectralEvalFiberOf P f₀ := by
  intro z hz
  have hzTranslated : z - (c : ℂ) ∈
      translatedSpectralSampleFinset P c := by
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hleft :
      zetaSpectralEval (convolutionAutocorrelation g) z =
        zetaSpectralEval (convolutionAutocorrelationShifted c g)
          (z - (c : ℂ)) := by
    have harg : (z - (c : ℂ)) + (c : ℂ) = z :=
      sub_add_cancel z (c : ℂ)
    calc
      zetaSpectralEval (convolutionAutocorrelation g) z =
          zetaSpectralEval (convolutionAutocorrelation g)
            ((z - (c : ℂ)) + (c : ℂ)) := by
        exact congrArg
          (fun q : ℂ => zetaSpectralEval
            (convolutionAutocorrelation g) q) harg.symm
      _ = zetaSpectralEval
          (exponentialModulate c (convolutionAutocorrelation g))
            (z - (c : ℂ)) := by
        exact (zetaSpectralEval_exponentialModulate c
          (convolutionAutocorrelation g) (z - (c : ℂ))).symm
      _ = zetaSpectralEval (convolutionAutocorrelationShifted c g)
            (z - (c : ℂ)) := by
        exact congrArg
          (fun q : ZetaAdmissibleFunction => zetaSpectralEval q
            (z - (c : ℂ)))
          (convolutionAutocorrelationShifted_eq_exponentialModulate c g).symm
  have hright :
      zetaSpectralEval (convolutionAutocorrelation f₀) z =
        zetaSpectralEval (convolutionAutocorrelationShifted c f₀)
          (z - (c : ℂ)) := by
    have harg : (z - (c : ℂ)) + (c : ℂ) = z :=
      sub_add_cancel z (c : ℂ)
    calc
      zetaSpectralEval (convolutionAutocorrelation f₀) z =
          zetaSpectralEval (convolutionAutocorrelation f₀)
            ((z - (c : ℂ)) + (c : ℂ)) := by
        exact congrArg
          (fun q : ℂ => zetaSpectralEval
            (convolutionAutocorrelation f₀) q) harg.symm
      _ = zetaSpectralEval
          (exponentialModulate c (convolutionAutocorrelation f₀))
            (z - (c : ℂ)) := by
        exact (zetaSpectralEval_exponentialModulate c
          (convolutionAutocorrelation f₀) (z - (c : ℂ))).symm
      _ = zetaSpectralEval (convolutionAutocorrelationShifted c f₀)
            (z - (c : ℂ)) := by
        exact congrArg
          (fun q : ZetaAdmissibleFunction => zetaSpectralEval q
            (z - (c : ℂ)))
          (convolutionAutocorrelationShifted_eq_exponentialModulate c f₀).symm
  calc
    zetaSpectralEval (convolutionAutocorrelation g) z =
        zetaSpectralEval (convolutionAutocorrelationShifted c g)
          (z - (c : ℂ)) := hleft
    _ = zetaSpectralEval (convolutionAutocorrelationShifted c f₀)
          (z - (c : ℂ)) := hg (z - (c : ℂ)) hzTranslated
    _ = zetaSpectralEval (convolutionAutocorrelation f₀) z := hright.symm

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
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε := by
  match
      exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported
        S P T₀ hT₀ ε hε A k hsum with
  | ⟨T, hT₀T, hT, htail⟩ =>
      exact ⟨T, hT₀T, hT, htail⟩

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
          φ = 0 := by
  exact
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
            (-(k + 3 : ℤ)) := by
  intro ρ
  match (inferInstance : Decidable
      (zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P)) with
  | isTrue hρDagger =>
      have hzero : zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0 :=
        hforced ρ hρDagger
      have hnormZero : ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ = 0 :=
        Eq.trans (congrArg norm hzero) norm_zero
      have henvNonnegative :
          0 ≤ A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)) :=
        zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ})
      exact le_trans (le_of_eq hnormZero) henvNonnegative
  | isFalse hρDagger =>
      exact hbound
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
          φ‖) := by
  let α := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}
  let contribution : α → ℂ :=
    fun ρ => zetaCenteredZeroSideContribution (ρ : ℂ)
      φ
  let envelope : α → ℝ :=
    fun ρ => A * zetaCompletedZeroCenteredHeight
      (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let zeroMap : α → {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun ρ => ⟨(ρ : ℂ), ρ.2.1⟩
  have hzeroMap : Function.Injective zeroMap := by
    intro left right heq
    exact Subtype.ext (congrArg (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (ρ : ℂ)) heq)
  have henvelope : Summable envelope := by
    have hcomposed := hsum.comp_injective hzeroMap
    have hcomposed_eq :
        ((fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∘ zeroMap) =
          envelope := by
      funext ρ
      exact Eq.refl (envelope ρ)
    exact Eq.subst
      (motive := fun sequence : α → ℝ => Summable sequence)
      hcomposed_eq
      hcomposed
  have hnormBound : ∀ ρ : α, ‖‖contribution ρ‖‖ ≤ envelope ρ := by
    intro ρ
    match (inferInstance : Decidable ((ρ : ℂ) ∈ T)) with
    | isTrue hρT =>
        have hzero : contribution ρ = 0 := hzeroT ρ hρT
        have hnormZero : ‖contribution ρ‖ = 0 :=
          Eq.trans (congrArg norm hzero) norm_zero
        have henvNonnegative : 0 ≤ envelope ρ :=
          zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ})
        exact le_trans
          (le_of_eq (norm_norm (contribution ρ)))
          (le_trans (le_of_eq hnormZero) henvNonnegative)
    | isFalse hρT =>
        have hboundρ : ‖contribution ρ‖ ≤ envelope ρ :=
          hbound ⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT⟩
        exact le_trans (le_of_eq (norm_norm (contribution ρ))) hboundρ
  exact Summable.of_norm_bounded envelope henvelope hnormBound

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
    ‖zetaCenteredZeroTail S φ‖ < ε := by
  have hwindowZero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaCenteredZeroSideContribution (ρ : ℂ) φ = 0 := by
    exact
      centered_window_zero_contribution_of_centered_window_vanishing
        S T φ hwindow
  have hgeneralBound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)) := by
    exact
      centered_zero_side_contribution_bound_of_forced_and_nonDagger
        S P T A k hA φ hforced hbound
  have hnormSummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          ‖zetaCenteredZeroSideContribution (ρ : ℂ) φ‖) := by
    exact
      centered_zero_side_contribution_norm_summable_of_window_vanishing
        S T A k hA hsum φ hwindowZero hgeneralBound
  have hcontributionSummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          zetaCenteredZeroSideContribution (ρ : ℂ) φ) := by
    exact Summable.of_norm hnormSummable
  have htailEq := zetaCenteredZeroTail_eq_complement_tsum_of_zero_on_window
    S T φ hcontributionSummable hwindowZero
  have htailLe :
      ‖zetaCenteredZeroTail S φ‖ ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)) := by
    calc
      ‖zetaCenteredZeroTail S φ‖ =
          ‖∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
            zetaCenteredZeroSideContribution (ρ : ℂ) φ‖ := by
        exact congrArg norm htailEq
      _ ≤
          ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                (-(k + 3 : ℤ)) := by
        exact
          zetaCenteredZeroTail_complement_norm_le_nonDagger_tsum
            S P T A k hA hsum φ hforced hbound
  exact lt_of_le_of_lt htailLe htail

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
              autocorrelationZeroTailRealAbs S f < ε := by
  obtain ⟨T, hT₀T, hT, htail⟩ :=
    centered_tail_window_selector_of_nonDagger_cutoff
      S P ε hε T₀ hT₀ A k hsum
  apply Exists.intro T
  apply And.intro hT₀T
  apply And.intro hT
  intro f hfFiber hfWindow
  have coordinateTransport :
      autocorrelationZeroTailRealAbs S f < ε := by
    have hfshiftedFiber :
        f ∈ AutocorrelationSpectralEvalFiberOfShifted
          (translatedSpectralSampleFinset P (1 / 2 : ℝ))
          (1 / 2 : ℝ) f₀ := by
      exact mem_autocorrelationSpectralEvalFiberOf_translatedModulation
        P (1 / 2 : ℝ) f₀ f hfFiber
    have hfplusWindow :
        ∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
            (zetaCenteredZero ρ) = 0 := by
      intro ρ hρ
      calc
        zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
            (zetaCenteredZero ρ) =
            zetaSpectralEval (convolutionAutocorrelation f) ρ := by
          exact zetaSpectralEval_positiveModulation_at_centeredZero f ρ
        _ = 0 := hfWindow ρ hρ
    have hplusForced :
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
            zetaCenteredZero (ρ : ℂ) ∈ daggerClosedSpectralSampleFinset P →
            zetaCenteredZeroSideContribution (ρ : ℂ)
              (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0 := by
      intro ρ hρ
      exact hpositiveForced f hfshiftedFiber
        (ρ : ℂ) ρ.2.1 ρ.2.2.1 hρ
    have hplusBound :
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T ∧
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          ‖zetaCenteredZeroSideContribution (ρ : ℂ)
              (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                (-(k + 3 : ℤ)) := by
      intro ρ
      have hρT₀ : (ρ : ℂ) ∉ T₀ := by
        intro hρT₀
        exact ρ.2.2.2.1 (hT₀T hρT₀)
      exact hpositiveEnv f hfshiftedFiber
        (fun σ hσT₀ => hfplusWindow σ (hT₀T hσT₀))
        ⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1, hρT₀⟩
    have hplusLt :
        ‖zetaCenteredZeroTail S
            (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ < ε := by
      exact centered_tail_bound_of_centered_window_vanishing
        S P T A k ε hA hsum htail
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
        hplusForced hplusBound hfplusWindow
    exact autocorrelationZeroTailRealAbs_lt_of_positiveModulation_centeredNorm_lt
      S f ε hplusLt
  exact coordinateTransport

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
              autocorrelationZeroTailRealAbs S f < ε := by
  match
      exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported
        S P T₀ hT₀ ε hε A k hsum with
  | ⟨T, hT₀T, hT, htail⟩ =>
      exact
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

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
