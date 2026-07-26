import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineInverseGammaChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineCorrectionScheduled
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanCriticalLineIntegrability

/-!
# Hermitian critical-line inverse-Gamma packet

The regular inverse-Gamma logarithmic derivative is paired with its critical-
line conjugate before it is split into archimedean and elementary correction
channels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The Hermitian inverse-Gamma logarithmic-derivative kernel. -/
noncomputable def zetaCompletedHermitianInverseGammaKernel
    (t : ℝ) : ℂ :=
  inverseGammaCompletionLogDeriv
      (zetaCompletedCenteredSpectralLine t) +
    star
      (inverseGammaCompletionLogDeriv
        (zetaCompletedCenteredSpectralLine t))

/-- The Hermitian elementary correction kernel. -/
noncomputable def zetaCompletedHermitianPoleCorrectionKernel
    (t : ℝ) : ℂ :=
  explicitFormulaCorrectionLogDerivative
      (zetaCompletedCenteredSpectralLine t) +
    star
      (explicitFormulaCorrectionLogDerivative
        (zetaCompletedCenteredSpectralLine t))

/-- The Hermitian inverse-Gamma critical-line integrand. -/
noncomputable def zetaCompletedHermitianInverseGammaIntegrand
    (probe : ZetaAdmissibleFunction)
    (t : ℝ) : ℂ :=
  zetaCompletedHermitianInverseGammaKernel t *
    zetaCompletedExplicitFormulaPhi probe (t * Complex.I)

/-- The Hermitian elementary correction critical-line integrand. -/
noncomputable def zetaCompletedHermitianPoleCorrectionIntegrand
    (probe : ZetaAdmissibleFunction)
    (t : ℝ) : ℂ :=
  zetaCompletedHermitianPoleCorrectionKernel t *
    zetaCompletedExplicitFormulaPhi probe (t * Complex.I)

/-- Conjugation commutes with the elementary rational correction. -/
theorem explicitFormulaCorrectionLogDerivative_star
    (s : ℂ) :
    star (explicitFormulaCorrectionLogDerivative s) =
      explicitFormulaCorrectionLogDerivative (star s) :=
  explicitFormulaCorrectionLogDerivative_star_shiftOwner s

/-- Subtracting a half-centered sum leaves the reflected centered
coordinate. -/
theorem complex_one_sub_half_add_eq_half_add_neg
    (z : ℂ) :
    1 - ((1 / 2 : ℂ) + z) = (1 / 2 : ℂ) + (-z) :=
  let halfEquality :
      (1 : ℂ) - (1 / 2 : ℂ) = (1 / 2 : ℂ) :=
    (eq_sub_iff_add_eq.mpr (add_halves (1 : ℂ))).symm
  let unfoldSub :
      1 - ((1 / 2 : ℂ) + z) =
        1 + (-((1 / 2 : ℂ) + z)) :=
    sub_eq_add_neg 1 ((1 / 2 : ℂ) + z)
  let distributeNeg :
      1 + (-((1 / 2 : ℂ) + z)) =
        1 + ((-(1 / 2 : ℂ)) + (-z)) :=
    congrArg (fun value : ℂ => 1 + value)
        (neg_add (1 / 2 : ℂ) z)
  let reassociate :
      1 + ((-(1 / 2 : ℂ)) + (-z)) =
        (1 + (-(1 / 2 : ℂ))) + (-z) :=
    (add_assoc 1 (-(1 / 2 : ℂ)) (-z)).symm
  let foldSub :
      (1 + (-(1 / 2 : ℂ))) + (-z) =
        (1 - (1 / 2 : ℂ)) + (-z) :=
    congrArg (fun value : ℂ => value + (-z))
        (sub_eq_add_neg 1 (1 / 2 : ℂ)).symm
  let foldHalf :
      (1 - (1 / 2 : ℂ)) + (-z) =
        (1 / 2 : ℂ) + (-z) :=
    congrArg (fun value : ℂ => value + (-z)) halfEquality
  Eq.trans unfoldSub
    (Eq.trans distributeNeg
      (Eq.trans reassociate
        (Eq.trans foldSub foldHalf)))

/-- Conjugation reflects the critical line through its center. -/
theorem zetaCompletedCenteredSpectralLine_star_eq_one_sub
    (t : ℝ) :
    star (zetaCompletedCenteredSpectralLine t) =
      1 - zetaCompletedCenteredSpectralLine t :=
  let coordinate : ℂ := (t : ℂ) * Complex.I
  let halfStar : star (1 / 2 : ℂ) = (1 / 2 : ℂ) :=
    let oneStar : star (1 : ℂ) = (1 : ℂ) :=
      star_one (R := ℂ)
    let twoStar : star (2 : ℂ) = (2 : ℂ) :=
      map_ofNat (starRingEnd ℂ) 2
    Eq.trans
      (star_div₀ (1 : ℂ) (2 : ℂ))
      (congrArg₂ HDiv.hDiv oneStar twoStar)
  let coordinateDagger : -star coordinate = coordinate :=
    zetaCompletedImaginaryCoordinate_dagger_fixed t
  let coordinateStar : star coordinate = -coordinate :=
    Eq.trans
      (neg_neg (star coordinate)).symm
      (congrArg Neg.neg coordinateDagger)
  let unfoldLine :
      star (zetaCompletedCenteredSpectralLine t) =
        star ((1 / 2 : ℂ) + coordinate) :=
    rfl
  let distributeStar :
      star ((1 / 2 : ℂ) + coordinate) =
        star (1 / 2 : ℂ) + star coordinate :=
    star_add (1 / 2 : ℂ) coordinate
  let coordinateTransport :
      star (1 / 2 : ℂ) + star coordinate =
        (1 / 2 : ℂ) + (-coordinate) :=
    congrArg₂ HAdd.hAdd halfStar coordinateStar
  let reflectCenter :
      (1 / 2 : ℂ) + (-coordinate) =
        1 - ((1 / 2 : ℂ) + coordinate) :=
    (complex_one_sub_half_add_eq_half_add_neg coordinate).symm
  let foldLine :
      1 - ((1 / 2 : ℂ) + coordinate) =
        1 - zetaCompletedCenteredSpectralLine t :=
    rfl
  Eq.trans unfoldLine
    (Eq.trans distributeStar
      (Eq.trans coordinateTransport
        (Eq.trans reflectCenter foldLine)))

/-- The elementary correction is skew-Hermitian on the critical line. -/
theorem explicitFormulaCorrectionLogDerivative_centered_star_eq_neg
    (t : ℝ) :
    star
        (explicitFormulaCorrectionLogDerivative
          (zetaCompletedCenteredSpectralLine t)) =
      -explicitFormulaCorrectionLogDerivative
        (zetaCompletedCenteredSpectralLine t) :=
  let spectralPoint : ℂ := zetaCompletedCenteredSpectralLine t
  let conjugateCorrection :
      star (explicitFormulaCorrectionLogDerivative spectralPoint) =
        explicitFormulaCorrectionLogDerivative (star spectralPoint) :=
    explicitFormulaCorrectionLogDerivative_star spectralPoint
  let reflectLine :
      explicitFormulaCorrectionLogDerivative (star spectralPoint) =
        explicitFormulaCorrectionLogDerivative (1 - spectralPoint) :=
    congrArg explicitFormulaCorrectionLogDerivative
        (zetaCompletedCenteredSpectralLine_star_eq_one_sub t)
  let oddCorrection :
      explicitFormulaCorrectionLogDerivative (1 - spectralPoint) =
        -explicitFormulaCorrectionLogDerivative spectralPoint :=
    explicitFormulaCorrectionLogDerivative_one_sub_eq_neg_shiftOwner
        spectralPoint
  Eq.trans conjugateCorrection
    (Eq.trans reflectLine oddCorrection)

/-- The Hermitian elementary correction kernel vanishes identically. -/
theorem zetaCompletedHermitianPoleCorrectionKernel_eq_zero
    (t : ℝ) :
    zetaCompletedHermitianPoleCorrectionKernel t = 0 :=
  let correction : ℂ :=
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedCenteredSpectralLine t)
  let reflectedEquality : star correction = -correction :=
    explicitFormulaCorrectionLogDerivative_centered_star_eq_neg t
  let unfoldKernel :
      zetaCompletedHermitianPoleCorrectionKernel t =
        correction + star correction :=
    rfl
  let substituteReflected :
      correction + star correction = correction + (-correction) :=
    congrArg (fun value : ℂ => correction + value) reflectedEquality
  Eq.trans unfoldKernel
    (Eq.trans substituteReflected (add_neg_cancel correction))

/-- The Hermitian elementary correction integrand vanishes identically. -/
theorem zetaCompletedHermitianPoleCorrectionIntegrand_eq_zero
    (probe : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedHermitianPoleCorrectionIntegrand probe t = 0 :=
  let unfoldIntegrand :
      zetaCompletedHermitianPoleCorrectionIntegrand probe t =
        zetaCompletedHermitianPoleCorrectionKernel t *
          zetaCompletedExplicitFormulaPhi probe (t * Complex.I) :=
    rfl
  let kernelZero :
      zetaCompletedHermitianPoleCorrectionKernel t *
          zetaCompletedExplicitFormulaPhi probe (t * Complex.I) =
        0 * zetaCompletedExplicitFormulaPhi probe (t * Complex.I) :=
    congrArg
        (fun value : ℂ =>
          value * zetaCompletedExplicitFormulaPhi probe (t * Complex.I))
        (zetaCompletedHermitianPoleCorrectionKernel_eq_zero t)
  Eq.trans unfoldIntegrand
    (Eq.trans kernelZero (zero_mul _))

/-- Two additive pairs regroup by channels. -/
theorem completedHermitianPair_regroup
    (archimedean correction reflectedArchimedean reflectedCorrection : ℂ) :
    (archimedean + correction) +
        (reflectedArchimedean + reflectedCorrection) =
      (archimedean + reflectedArchimedean) +
        (correction + reflectedCorrection) :=
  let reassociateLeft :
      (archimedean + correction) +
        (reflectedArchimedean + reflectedCorrection) =
        archimedean +
          (correction + (reflectedArchimedean + reflectedCorrection)) :=
    add_assoc archimedean correction
        (reflectedArchimedean + reflectedCorrection)
  let middleEquality :
          correction + (reflectedArchimedean + reflectedCorrection) =
            reflectedArchimedean + (correction + reflectedCorrection) :=
    let firstAssoc :
        correction + (reflectedArchimedean + reflectedCorrection) =
          (correction + reflectedArchimedean) + reflectedCorrection :=
      (add_assoc correction reflectedArchimedean reflectedCorrection).symm
    let commuteMiddle :
        (correction + reflectedArchimedean) + reflectedCorrection =
          (reflectedArchimedean + correction) + reflectedCorrection :=
      congrArg
              (fun value : ℂ => value + reflectedCorrection)
              (add_comm correction reflectedArchimedean)
    let secondAssoc :
        (reflectedArchimedean + correction) + reflectedCorrection =
          reflectedArchimedean + (correction + reflectedCorrection) :=
      add_assoc reflectedArchimedean correction reflectedCorrection
    Eq.trans firstAssoc
      (Eq.trans commuteMiddle secondAssoc)
  let moveMiddle :
      archimedean +
          (correction + (reflectedArchimedean + reflectedCorrection)) =
        archimedean +
          (reflectedArchimedean + (correction + reflectedCorrection)) :=
    congrArg (fun value : ℂ => archimedean + value) middleEquality
  let reassociateRight :
      archimedean +
          (reflectedArchimedean + (correction + reflectedCorrection)) =
        (archimedean + reflectedArchimedean) +
          (correction + reflectedCorrection) :=
    (add_assoc archimedean reflectedArchimedean
        (correction + reflectedCorrection)).symm
  Eq.trans reassociateLeft
    (Eq.trans moveMiddle reassociateRight)

/-- The Hermitian inverse-Gamma integrand splits pointwise into the Hermitian
archimedean and elementary correction integrands. -/
theorem zetaCompletedHermitianInverseGammaIntegrand_eq_archimedean_add_correction
    (probe : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedHermitianInverseGammaIntegrand probe t =
      zetaCompletedArchimedeanHermitianIntegrand probe t +
        zetaCompletedHermitianPoleCorrectionIntegrand probe t :=
  let spectralPoint : ℂ := zetaCompletedCenteredSpectralLine t
  let inverseGamma : ℂ := inverseGammaCompletionLogDeriv spectralPoint
  let archimedean : ℂ := explicitFormulaArchimedeanLogDerivative spectralPoint
  let correction : ℂ := explicitFormulaCorrectionLogDerivative spectralPoint
  let transformValue : ℂ :=
    zetaCompletedExplicitFormulaPhi probe (t * Complex.I)
  let channelEquality : inverseGamma = archimedean + correction :=
    let archimedeanEquality : archimedean = inverseGamma - correction :=
      explicitFormulaArchimedeanLogDerivative_eq_inverseGammaCorrection_sub_poleCorrection
        spectralPoint
    Eq.trans (sub_add_cancel inverseGamma correction).symm
      (congrArg (fun value : ℂ => value + correction)
        archimedeanEquality.symm)
  let reflectedEquality :
      star inverseGamma = star archimedean + star correction :=
    Eq.trans (congrArg star channelEquality)
      (star_add archimedean correction)
  let pairedEquality :
      inverseGamma + star inverseGamma =
        (archimedean + star archimedean) +
          (correction + star correction) :=
    Eq.trans
      (congrArg₂ HAdd.hAdd channelEquality reflectedEquality)
      (completedHermitianPair_regroup
        archimedean correction (star archimedean) (star correction))
  let unfoldIntegrand :
      zetaCompletedHermitianInverseGammaIntegrand probe t =
        (inverseGamma + star inverseGamma) * transformValue :=
    rfl
  let channelTransport :
      (inverseGamma + star inverseGamma) * transformValue =
        ((archimedean + star archimedean) +
          (correction + star correction)) * transformValue :=
    congrArg (fun value : ℂ => value * transformValue) pairedEquality
  let distribute :
      ((archimedean + star archimedean) +
          (correction + star correction)) * transformValue =
        (archimedean + star archimedean) * transformValue +
          (correction + star correction) * transformValue :=
    add_mul
        (archimedean + star archimedean)
        (correction + star correction)
        transformValue
  let foldRight :
      (archimedean + star archimedean) * transformValue +
          (correction + star correction) * transformValue =
        zetaCompletedArchimedeanHermitianIntegrand probe t +
          zetaCompletedHermitianPoleCorrectionIntegrand probe t :=
    rfl
  Eq.trans unfoldIntegrand
    (Eq.trans channelTransport
      (Eq.trans distribute foldRight))

/-- On the critical line the Hermitian inverse-Gamma integrand is exactly the
Hermitian archimedean integrand. -/
theorem zetaCompletedHermitianInverseGammaIntegrand_eq_archimedean
    (probe : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedHermitianInverseGammaIntegrand probe t =
      zetaCompletedArchimedeanHermitianIntegrand probe t :=
  let split :
      zetaCompletedHermitianInverseGammaIntegrand probe t =
        zetaCompletedArchimedeanHermitianIntegrand probe t +
          zetaCompletedHermitianPoleCorrectionIntegrand probe t :=
    zetaCompletedHermitianInverseGammaIntegrand_eq_archimedean_add_correction
      probe t
  let zeroCorrection :
      zetaCompletedArchimedeanHermitianIntegrand probe t +
          zetaCompletedHermitianPoleCorrectionIntegrand probe t =
        zetaCompletedArchimedeanHermitianIntegrand probe t + 0 :=
    congrArg
        (fun value : ℂ =>
          zetaCompletedArchimedeanHermitianIntegrand probe t + value)
        (zetaCompletedHermitianPoleCorrectionIntegrand_eq_zero probe t)
  Eq.trans split
    (Eq.trans zeroCorrection (add_zero _))

/-- The whole-line Hermitian inverse-Gamma value is the public Hermitian
archimedean contribution. -/
theorem zetaCompletedHermitianInverseGammaIntegrand_integral_eq_archimedeanContribution
    (probe : ZetaAdmissibleFunction) :
    (∫ t : ℝ,
      zetaCompletedHermitianInverseGammaIntegrand probe t) =
      zetaCompletedExplicitFormulaArchimedeanContribution probe :=
  let functionEquality :
      zetaCompletedHermitianInverseGammaIntegrand probe =
        zetaCompletedArchimedeanHermitianIntegrand probe :=
    funext
      (fun t : ℝ =>
        zetaCompletedHermitianInverseGammaIntegrand_eq_archimedean probe t)
  Eq.trans
    (congrArg
      (fun integrand : ℝ → ℂ => ∫ t : ℝ, integrand t)
      functionEquality)
    rfl

/-- The Hermitian elementary correction kernel is strongly measurable. -/
theorem zetaCompletedHermitianPoleCorrectionKernel_aestronglyMeasurable :
    AEStronglyMeasurable
      zetaCompletedHermitianPoleCorrectionKernel
      (volume : Measure ℝ) :=
  let correction : ℝ → ℂ := fun t : ℝ =>
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedCenteredSpectralLine t)
  let correctionMeasurable :
      AEStronglyMeasurable correction (volume : Measure ℝ) :=
    zetaCompletedCenteredElementaryPoleCorrection_aestronglyMeasurable
  let conjugateMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ => star (correction t))
        (volume : Measure ℝ) :=
    continuous_star.comp_aestronglyMeasurable correctionMeasurable
  let sumMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ => correction t + star (correction t))
        (volume : Measure ℝ) :=
    correctionMeasurable.add conjugateMeasurable
  Eq.subst
    (motive := fun candidate : ℝ → ℂ =>
      AEStronglyMeasurable candidate (volume : Measure ℝ))
    (show zetaCompletedHermitianPoleCorrectionKernel =
      (fun t : ℝ => correction t + star (correction t)) from rfl).symm
    sumMeasurable

/-- The Hermitian elementary correction kernel has a doubled linear bound. -/
theorem zetaCompletedHermitianPoleCorrectionKernel_bound
    (t : ℝ) :
    ‖zetaCompletedHermitianPoleCorrectionKernel t‖ ≤
      (2 * zetaCompletedCenteredElementaryPoleBoundConstant) *
        (1 + ‖t‖) :=
  let correction : ℂ :=
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedCenteredSpectralLine t)
  let bound : ℝ :=
    zetaCompletedCenteredElementaryPoleBoundConstant * (1 + ‖t‖)
  let correctionEquality :
      correction =
        (-1 : ℂ) / zetaCompletedCenteredSpectralLine t -
          1 / (zetaCompletedCenteredSpectralLine t - 1) :=
    explicitFormulaCorrectionLogDerivative_eq_poleCorrection
      (zetaCompletedCenteredSpectralLine t)
  let correctionBound : ‖correction‖ ≤ bound :=
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ bound)
      correctionEquality.symm
      (zetaCompletedCenteredElementaryPoleCorrection_bound t)
  let conjugateNorm : ‖star correction‖ = ‖correction‖ :=
    norm_star correction
  let conjugateBound : ‖star correction‖ ≤ bound :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ bound)
      conjugateNorm.symm
      correctionBound
  let sumBound :
      ‖correction + star correction‖ ≤ bound + bound :=
    le_trans (norm_add_le correction (star correction))
      (add_le_add correctionBound conjugateBound)
  let doubleBound :
      bound + bound =
        (2 * zetaCompletedCenteredElementaryPoleBoundConstant) *
          (1 + ‖t‖) :=
    let double :
        bound + bound = 2 * bound :=
      (two_mul bound).symm
    let reassociate :
        2 * bound =
          (2 * zetaCompletedCenteredElementaryPoleBoundConstant) *
            (1 + ‖t‖) :=
      (mul_assoc 2
          zetaCompletedCenteredElementaryPoleBoundConstant
          (1 + ‖t‖)).symm
    Eq.trans double reassociate
  let kernelEquality :
      zetaCompletedHermitianPoleCorrectionKernel t =
        correction + star correction :=
    rfl
  Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        (2 * zetaCompletedCenteredElementaryPoleBoundConstant) *
          (1 + ‖t‖))
    kernelEquality.symm
    (sumBound.trans_eq doubleBound)

/-- The Hermitian elementary correction integrand is integrable. -/
theorem zetaCompletedHermitianPoleCorrectionIntegrand_integrable
    (probe : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedHermitianPoleCorrectionIntegrand probe)
      (volume : Measure ℝ) :=
  zetaCompletedCriticalLineProduct_integrable_of_linearFactor
    probe
    zetaCompletedHermitianPoleCorrectionKernel
    (2 * zetaCompletedCenteredElementaryPoleBoundConstant)
    (mul_nonneg zero_le_two
      zetaCompletedCenteredElementaryPoleBoundConstant_nonneg)
    zetaCompletedHermitianPoleCorrectionKernel_aestronglyMeasurable
    zetaCompletedHermitianPoleCorrectionKernel_bound

/-- The Hermitian inverse-Gamma critical-line integrand is integrable. -/
theorem zetaCompletedHermitianInverseGammaIntegrand_integrable
    (probe : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedHermitianInverseGammaIntegrand probe)
      (volume : Measure ℝ) :=
  let sumIntegrable :
      Integrable
        (fun t : ℝ =>
          zetaCompletedArchimedeanHermitianIntegrand probe t +
            zetaCompletedHermitianPoleCorrectionIntegrand probe t)
        (volume : Measure ℝ) :=
    (zetaCompletedArchimedeanHermitianIntegrand_integrable probe).add
      (zetaCompletedHermitianPoleCorrectionIntegrand_integrable probe)
  let functionEquality :
      zetaCompletedHermitianInverseGammaIntegrand probe =
        fun t : ℝ =>
          zetaCompletedArchimedeanHermitianIntegrand probe t +
            zetaCompletedHermitianPoleCorrectionIntegrand probe t :=
    funext
      (fun t : ℝ =>
        zetaCompletedHermitianInverseGammaIntegrand_eq_archimedean_add_correction
          probe t)
  Eq.subst
    (motive := fun candidate : ℝ → ℂ =>
      Integrable candidate (volume : Measure ℝ))
    functionEquality.symm
    sumIntegrable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
