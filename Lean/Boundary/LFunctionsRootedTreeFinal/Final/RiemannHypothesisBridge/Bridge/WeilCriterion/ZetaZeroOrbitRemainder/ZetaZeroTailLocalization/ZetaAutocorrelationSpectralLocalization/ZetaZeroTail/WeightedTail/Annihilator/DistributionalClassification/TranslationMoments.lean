import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.GlobalTranslationCharacter
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Modulation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Owner

/-!
# Translation moments of a completed-zero distribution

Physical translation multiplies each completed-zero coordinate by its scaled
exponential character.  Thus annihilator values on integer translates are the
moments of an absolutely summable seeded coefficient family.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

noncomputable def completedZeroTranslationSeededCoefficient
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (f : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate) : ℂ :=
  b rho * zetaZeroSideContribution (rho : ℂ) f

noncomputable def completedZeroTranslationMomentSeries
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (delta : ℝ)
    (f : ZetaAdmissibleFunction)
    (k : ℕ)
    (rho : ZetaCompletedZeroCoordinate) : ℂ :=
  completedZeroTranslationSeededCoefficient b f rho *
    zetaScaledTranslateCharacter delta (rho : ℂ) ^ k

theorem zetaZeroSideContribution_translate
    (c : ℝ)
    (f : ZetaAdmissibleFunction)
    (rho : ℂ) :
    zetaZeroSideContribution rho (translate c f) =
      Complex.exp (-(rho * (c : ℂ))) * zetaZeroSideContribution rho f := by
  have hspectralTranslate :
      zetaSpectralEval (translate c f) rho =
        Complex.exp (-(rho * (c : ℂ))) * zetaSpectralEval f rho := by
    have htranslatedLaplace :=
      Boundary.zetaLaplaceTransform_translate c f rho
    have htranslatedSpectral :=
      zetaSpectralEval_eq_laplace (translate c f) rho
    have horiginalSpectral :=
      zetaSpectralEval_eq_laplace f rho
    exact Eq.trans htranslatedSpectral
      (Eq.trans htranslatedLaplace
        (congrArg
          (fun value : ℂ => Complex.exp (-(rho * (c : ℂ))) * value)
          horiginalSpectral.symm))
  unfold zetaZeroSideContribution
  have hassociate :
      -((zetaZeroMultiplicity rho : ℂ)) *
          (Complex.exp (-(rho * (c : ℂ))) * zetaSpectralEval f rho) =
        (-((zetaZeroMultiplicity rho : ℂ)) *
          Complex.exp (-(rho * (c : ℂ)))) * zetaSpectralEval f rho :=
    (mul_assoc
      (-((zetaZeroMultiplicity rho : ℂ)))
      (Complex.exp (-(rho * (c : ℂ))))
      (zetaSpectralEval f rho)).symm
  have hcoefficientCommutes :
      (-((zetaZeroMultiplicity rho : ℂ)) *
          Complex.exp (-(rho * (c : ℂ)))) * zetaSpectralEval f rho =
        (Complex.exp (-(rho * (c : ℂ))) *
          -((zetaZeroMultiplicity rho : ℂ))) * zetaSpectralEval f rho :=
    congrArg
      (fun value : ℂ => value * zetaSpectralEval f rho)
      (mul_comm
        (-((zetaZeroMultiplicity rho : ℂ)))
        (Complex.exp (-(rho * (c : ℂ)))))
  have hfactor :
      (Complex.exp (-(rho * (c : ℂ))) *
          -((zetaZeroMultiplicity rho : ℂ))) * zetaSpectralEval f rho =
        Complex.exp (-(rho * (c : ℂ))) *
          (-((zetaZeroMultiplicity rho : ℂ)) * zetaSpectralEval f rho) :=
    mul_assoc
      (Complex.exp (-(rho * (c : ℂ))))
      (-((zetaZeroMultiplicity rho : ℂ)))
      (zetaSpectralEval f rho)
  have hspectralSubstitution :
      -((zetaZeroMultiplicity rho : ℂ)) *
          zetaSpectralEval (translate c f) rho =
        -((zetaZeroMultiplicity rho : ℂ)) *
          (Complex.exp (-(rho * (c : ℂ))) * zetaSpectralEval f rho) :=
    congrArg
      (fun spectralValue : ℂ =>
        -((zetaZeroMultiplicity rho : ℂ)) * spectralValue)
      hspectralTranslate
  exact Eq.trans hspectralSubstitution
    (Eq.trans hassociate (Eq.trans hcoefficientCommutes hfactor))

theorem completedZeroTranslationMomentSeries_eq_translatedAnnihilatorTerm
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (delta : ℝ)
    (f : ZetaAdmissibleFunction)
    (k : ℕ)
    (rho : ZetaCompletedZeroCoordinate) :
    completedZeroTranslationMomentSeries b delta f k rho =
      b rho * zetaZeroSideContribution (rho : ℂ)
        (translate ((k : ℝ) * delta) f) := by
  have hsideTranslate :=
    zetaZeroSideContribution_translate ((k : ℝ) * delta) f (rho : ℂ)
  have hcharacterPower :=
    zetaScaledTranslateCharacter_pow delta (rho : ℂ) k
  unfold completedZeroTranslationMomentSeries
  unfold completedZeroTranslationSeededCoefficient
  have hassociate :
      (b rho * zetaZeroSideContribution (rho : ℂ) f) *
          zetaScaledTranslateCharacter delta (rho : ℂ) ^ k =
        b rho *
          (zetaZeroSideContribution (rho : ℂ) f *
            zetaScaledTranslateCharacter delta (rho : ℂ) ^ k) :=
    mul_assoc
      (b rho)
      (zetaZeroSideContribution (rho : ℂ) f)
      (zetaScaledTranslateCharacter delta (rho : ℂ) ^ k)
  have hinsideCharacter :
      zetaZeroSideContribution (rho : ℂ) f *
          zetaScaledTranslateCharacter delta (rho : ℂ) ^ k =
        zetaZeroSideContribution (rho : ℂ) f *
          Complex.exp (-((rho : ℂ) * (((k : ℝ) * delta : ℝ) : ℂ))) :=
    congrArg
      (fun value : ℂ => zetaZeroSideContribution (rho : ℂ) f * value)
      hcharacterPower
  have hinsideCommutes :
      zetaZeroSideContribution (rho : ℂ) f *
          Complex.exp (-((rho : ℂ) * (((k : ℝ) * delta : ℝ) : ℂ))) =
        Complex.exp (-((rho : ℂ) * (((k : ℝ) * delta : ℝ) : ℂ))) *
          zetaZeroSideContribution (rho : ℂ) f :=
    mul_comm
      (zetaZeroSideContribution (rho : ℂ) f)
      (Complex.exp (-((rho : ℂ) * (((k : ℝ) * delta : ℝ) : ℂ))))
  have hinsideTranslated :
      Complex.exp (-((rho : ℂ) * (((k : ℝ) * delta : ℝ) : ℂ))) *
          zetaZeroSideContribution (rho : ℂ) f =
        zetaZeroSideContribution (rho : ℂ) (translate ((k : ℝ) * delta) f) :=
    hsideTranslate.symm
  exact Eq.trans hassociate
    (congrArg
      (fun value : ℂ => b rho * value)
      (Eq.trans hinsideCharacter
        (Eq.trans hinsideCommutes hinsideTranslated)))

theorem completedZeroTranslationMomentSeries_eq_shiftedSeries_zero_translate
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (delta : ℝ)
    (f : ZetaAdmissibleFunction)
    (k : ℕ)
    (rho : ZetaCompletedZeroCoordinate) :
    completedZeroTranslationMomentSeries b delta f k rho =
      completedZeroShiftedAnnihilatorSeries b 0
        (translate ((k : ℝ) * delta) f) rho := by
  have htranslatedTerm :=
    completedZeroTranslationMomentSeries_eq_translatedAnnihilatorTerm
      b delta f k rho
  have hzeroSubtraction : (rho : ℂ) - 0 = (rho : ℂ) :=
    sub_zero (rho : ℂ)
  unfold completedZeroShiftedAnnihilatorSeries
  unfold zetaZeroSideContribution at htranslatedTerm
  exact Eq.trans htranslatedTerm
    (congrArg
      (fun spectralPoint : ℂ =>
        b rho *
          (-((zetaZeroMultiplicity (rho : ℂ) : ℂ)) *
            zetaSpectralEval (translate ((k : ℝ) * delta) f) spectralPoint))
      hzeroSubtraction.symm)

theorem summable_completedZeroTranslationMomentSeries
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (delta : ℝ)
    (f : ZetaAdmissibleFunction)
    (k : ℕ) :
    Summable (completedZeroTranslationMomentSeries b delta f k) := by
  have htranslatedSummable :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (translate ((k : ℝ) * delta) f)
  have hseriesEquality :
      completedZeroTranslationMomentSeries b delta f k =
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * zetaZeroSideContribution (rho : ℂ)
            (translate ((k : ℝ) * delta) f)) :=
    funext
      (fun rho : ZetaCompletedZeroCoordinate =>
        completedZeroTranslationMomentSeries_eq_translatedAnnihilatorTerm
          b delta f k rho)
  exact Eq.mpr (congrArg Summable hseriesEquality.symm) htranslatedSummable

theorem completedZeroTranslationMoment_tsum_eq_annihilator_translate
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (delta : ℝ)
    (f : ZetaAdmissibleFunction)
    (k : ℕ) :
    tsum (completedZeroTranslationMomentSeries b delta f k) =
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        (translate ((k : ℝ) * delta) f) := by
  have htermTsum :
      tsum (completedZeroTranslationMomentSeries b delta f k) =
        tsum
          (fun rho : ZetaCompletedZeroCoordinate =>
            b rho * zetaZeroSideContribution (rho : ℂ)
              (translate ((k : ℝ) * delta) f)) :=
    tsum_congr
      (fun rho : ZetaCompletedZeroCoordinate =>
        completedZeroTranslationMomentSeries_eq_translatedAnnihilatorTerm
          b delta f k rho)
  have hannihilatorTsum :=
    zetaCompletedZeroSideAnnihilator_eq_tsum
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (translate ((k : ℝ) * delta) f)
  exact Eq.trans htermTsum hannihilatorTsum.symm

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
