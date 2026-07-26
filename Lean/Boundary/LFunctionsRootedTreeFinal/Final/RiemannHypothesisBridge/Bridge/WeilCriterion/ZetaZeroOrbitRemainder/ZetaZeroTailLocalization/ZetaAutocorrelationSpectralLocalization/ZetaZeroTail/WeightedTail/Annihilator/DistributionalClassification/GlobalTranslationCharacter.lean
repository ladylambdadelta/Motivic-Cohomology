import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.FiniteExponentialDetector.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.DualPairing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Owner

/-!
# Global translation character for completed zeros

The completed-zero set is countable because it is the union of its finite
natural-radius centered-height balls.  This is the countability input for
choosing one translation scale outside all exponential-period collisions.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem completedZeroCoordinate_univ_eq_iUnion_centeredHeightBall :
    (Set.univ : Set ZetaCompletedZeroCoordinate) =
      ⋃ n : ℕ, completedZerosInCenteredHeightBall (n : ℝ) := by
  exact Set.ext (fun rho =>
    Iff.intro
      (fun hrho =>
        have hn : ∃ n : ℕ,
            zetaCompletedZeroCenteredHeight rho ≤ (n : ℝ) :=
          exists_nat_ge (zetaCompletedZeroCenteredHeight rho)
        match hn with
        | ⟨n, hheight⟩ =>
            Set.mem_iUnion.mpr ⟨n, hheight⟩)
      (fun hrho => Set.mem_univ rho))

theorem countable_completedZeroCoordinate_univ :
    (Set.univ : Set ZetaCompletedZeroCoordinate).Countable := by
  have hballsCountable :
      ∀ n : ℕ,
        (completedZerosInCenteredHeightBall (n : ℝ)).Countable :=
    fun n : ℕ =>
      (finite_completedZerosInCenteredHeightBall (n : ℝ)).countable
  have hunionCountable :
      (⋃ n : ℕ, completedZerosInCenteredHeightBall (n : ℝ)).Countable :=
    Set.countable_iUnion hballsCountable
  exact Eq.mpr
    (congrArg Set.Countable
      completedZeroCoordinate_univ_eq_iUnion_centeredHeightBall)
    hunionCountable

theorem countable_completedZeroCoordinate : Countable ZetaCompletedZeroCoordinate :=
  Set.countable_univ_iff.mp countable_completedZeroCoordinate_univ

theorem zetaCenteredZero_im_eq_completedZero_im
    (rho : ZetaCompletedZeroCoordinate) :
    (zetaCenteredZero (rho : ℂ)).im = (rho : ℂ).im := by
  have hsubImaginary :
      ((rho : ℂ) - (1 / 2 : ℂ)).im =
        (rho : ℂ).im - (1 / 2 : ℂ).im :=
    Complex.sub_im (rho : ℂ) (1 / 2 : ℂ)
  have hhalfImaginary : (1 / 2 : ℂ).im = 0 := by
    have hhalfComplex : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
      (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm
    exact Eq.trans
      (congrArg Complex.im hhalfComplex)
      (Complex.ofReal_im (1 / 2 : ℝ))
  unfold zetaCenteredZero
  exact Eq.trans hsubImaginary
    (Eq.trans
      (congrArg (fun value : ℝ => (rho : ℂ).im - value) hhalfImaginary)
      (sub_zero (rho : ℂ).im))

theorem finite_completedZeroCoordinate_imaginaryBand
    (R : ℝ) :
    Set.Finite
      {rho : ZetaCompletedZeroCoordinate | |(rho : ℂ).im| ≤ R} := by
  have hsubset :
      {rho : ZetaCompletedZeroCoordinate | |(rho : ℂ).im| ≤ R} ⊆
        completedZerosInCenteredHeightBall (1 + R) := by
    intro rho hrho
    unfold completedZerosInCenteredHeightBall
    unfold zetaCompletedZeroCenteredHeight
    have hcenteredImaginary := zetaCenteredZero_im_eq_completedZero_im rho
    have hnormIdentity :
        norm ((zetaCenteredZero (rho : ℂ)).im) = |(rho : ℂ).im| := by
      exact Eq.trans
        (congrArg norm hcenteredImaginary)
        (Real.norm_eq_abs (rho : ℂ).im)
    have haddBound : 1 + |(rho : ℂ).im| ≤ 1 + R :=
      add_le_add_left hrho 1
    exact Eq.subst
      (motive := fun value : ℝ => 1 + value ≤ 1 + R)
      hnormIdentity.symm
      haddBound
  exact Set.Finite.subset
    (finite_completedZerosInCenteredHeightBall (1 + R))
    hsubset

noncomputable def completedZeroTranslationPeriodScale
    (rho eta : ZetaCompletedZeroCoordinate)
    (m : ℤ) : ℝ :=
  ((m : ℝ) * (2 * Real.pi)) / ((eta : ℂ) - (rho : ℂ)).im

def completedZeroTranslationForbiddenScales : Set ℝ :=
  {0} ∪
    Set.range
      (fun data : ZetaCompletedZeroCoordinate × ZetaCompletedZeroCoordinate × ℤ =>
        completedZeroTranslationPeriodScale data.1 data.2.1 data.2.2)

theorem countable_completedZeroTranslationForbiddenScales :
    completedZeroTranslationForbiddenScales.Countable := by
  letI : Countable ZetaCompletedZeroCoordinate :=
    countable_completedZeroCoordinate
  have hzeroCountable : ({0} : Set ℝ).Countable :=
    Set.countable_singleton 0
  have hrangeCountable :
      (Set.range
        (fun data : ZetaCompletedZeroCoordinate × ZetaCompletedZeroCoordinate × ℤ =>
          completedZeroTranslationPeriodScale data.1 data.2.1 data.2.2)).Countable :=
    Set.countable_range
      (fun data : ZetaCompletedZeroCoordinate × ZetaCompletedZeroCoordinate × ℤ =>
        completedZeroTranslationPeriodScale data.1 data.2.1 data.2.2)
  exact hzeroCountable.union hrangeCountable

theorem exists_scale_outside_completedZeroTranslationForbiddenScales :
    ∃ delta : ℝ, delta ∉ completedZeroTranslationForbiddenScales := by
  have hcountable : completedZeroTranslationForbiddenScales.Countable :=
    countable_completedZeroTranslationForbiddenScales
  have hnotUniv : completedZeroTranslationForbiddenScales ≠ Set.univ :=
    fun huniv =>
      Set.not_countable_univ
        (Eq.mpr
          (congrArg Set.Countable huniv.symm)
          hcountable)
  exact
    (Set.ne_univ_iff_exists_not_mem completedZeroTranslationForbiddenScales).mp hnotUniv

theorem completedZeroTranslationPeriodScale_eq_of_character_eq
    (delta : ℝ)
    (hdeltaNonzero : delta ≠ 0)
    (rho eta : ZetaCompletedZeroCoordinate)
    (hrhoEta : rho ≠ eta)
    (hcharacter :
      zetaScaledTranslateCharacter delta (rho : ℂ) =
        zetaScaledTranslateCharacter delta (eta : ℂ)) :
    ∃ m : ℤ,
      delta = completedZeroTranslationPeriodScale rho eta m := by
  have hrealEqual : (rho : ℂ).re = (eta : ℂ).re :=
    zetaScaledTranslateCharacter_eq_forces_re_eq hdeltaNonzero hcharacter
  have himaginaryNe : ((eta : ℂ) - (rho : ℂ)).im ≠ 0 := by
    intro himaginaryZero
    have himaginaryEqual : (eta : ℂ).im = (rho : ℂ).im := by
      have hdifferenceImaginary :
          ((eta : ℂ) - (rho : ℂ)).im =
            (eta : ℂ).im - (rho : ℂ).im :=
        Complex.sub_im (eta : ℂ) (rho : ℂ)
      have hsubZero : (eta : ℂ).im - (rho : ℂ).im = 0 :=
        Eq.trans hdifferenceImaginary.symm himaginaryZero
      exact sub_eq_zero.mp hsubZero
    have hvalueEqual : (rho : ℂ) = (eta : ℂ) :=
      Complex.ext hrealEqual himaginaryEqual.symm
    exact hrhoEta (Subtype.ext hvalueEqual)
  match
      (zetaScaledTranslateCharacter_eq_iff_exists_period
        delta (rho : ℂ) (eta : ℂ)).mp hcharacter with
  | ⟨m, hperiod⟩ =>
      have hdifferencePeriod :
          ((eta : ℂ) - (rho : ℂ)) * (delta : ℂ) =
            m * (2 * Real.pi * Complex.I) :=
        zetaScaledTranslateExponent_period_to_difference hperiod
      have himaginaryPeriod :
          ((eta : ℂ) - (rho : ℂ)).im * delta =
            (m : ℝ) * (2 * Real.pi) :=
        zetaScaledDifference_period_im_eq_int_two_pi hdifferencePeriod
      have hdeltaTimesImaginary :
          delta * ((eta : ℂ) - (rho : ℂ)).im =
            (m : ℝ) * (2 * Real.pi) :=
        Eq.trans
          (mul_comm delta ((eta : ℂ) - (rho : ℂ)).im)
          himaginaryPeriod
      have hscale :
          delta =
            ((m : ℝ) * (2 * Real.pi)) /
              ((eta : ℂ) - (rho : ℂ)).im :=
        (eq_div_iff himaginaryNe).mpr hdeltaTimesImaginary
      exact ⟨m, hscale⟩

theorem exists_globallyInjective_completedZeroTranslationCharacter :
    ∃ delta : ℝ,
      delta ≠ 0 ∧
        Function.Injective
          (fun rho : ZetaCompletedZeroCoordinate =>
            zetaScaledTranslateCharacter delta (rho : ℂ)) := by
  match exists_scale_outside_completedZeroTranslationForbiddenScales with
  | ⟨delta, hdeltaAllowed⟩ =>
      have hdeltaNonzero : delta ≠ 0 :=
        fun hdeltaZero => hdeltaAllowed (Or.inl hdeltaZero)
      have hinjective :
          Function.Injective
            (fun rho : ZetaCompletedZeroCoordinate =>
              zetaScaledTranslateCharacter delta (rho : ℂ)) :=
        fun rho eta hcharacter =>
          not_ne_iff.mp
            (fun hrhoEta =>
            match
                completedZeroTranslationPeriodScale_eq_of_character_eq
                  delta hdeltaNonzero rho eta hrhoEta hcharacter with
            | ⟨m, hscale⟩ =>
                have hrange : delta ∈
                    Set.range
                      (fun data : ZetaCompletedZeroCoordinate ×
                          ZetaCompletedZeroCoordinate × ℤ =>
                        completedZeroTranslationPeriodScale
                          data.1 data.2.1 data.2.2) :=
                  ⟨(rho, eta, m), hscale.symm⟩
                hdeltaAllowed (Or.inr hrange))
      exact ⟨delta, hdeltaNonzero, hinjective⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
