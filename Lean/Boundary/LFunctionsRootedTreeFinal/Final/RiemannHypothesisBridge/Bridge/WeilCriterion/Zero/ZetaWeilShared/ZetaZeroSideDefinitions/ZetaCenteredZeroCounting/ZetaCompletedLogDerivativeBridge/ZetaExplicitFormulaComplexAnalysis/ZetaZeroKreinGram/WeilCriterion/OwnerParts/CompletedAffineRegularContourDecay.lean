import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourGammaBound
import Mathlib.Topology.Basic

/-!
# Horizontal decay for the regular inverse-Gamma contour

This file integrates the inverse-quadratic compact-strip carrier majorant and
owns the vanishing of the two horizontal edges.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Either horizontal edge integral inherits the inverse-quadratic carrier
majorant, multiplied only by the fixed strip volume. -/
theorem regularInverseGamma_horizontalEdgeIntegral_norm_bound
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (K : ℝ)
    (carrierBound :
      ∀ x T : ℝ,
        x ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖zetaCompletedRegularInverseGammaContourCarrier f
            ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          K * (1 + ‖T‖) ^ (-(2 : ℤ)))
    (T : ℝ) :
    ‖∫ x in Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)),
        zetaCompletedRegularInverseGammaContourCarrier f
          ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      (K * (1 + ‖T‖) ^ (-(2 : ℤ))) *
        (volume
          (Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)))).toReal :=
  MeasureTheory.norm_setIntegral_le_of_norm_le_const'
    (μ := volume)
    (s := Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)))
    (f := fun x : ℝ =>
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + (T : ℂ) * Complex.I))
    (C := K * (1 + ‖T‖) ^ (-(2 : ℤ)))
    measure_Icc_lt_top measurableSet_Icc
    (fun x membership => carrierBound x T membership)

/-- The oriented horizontal defect is bounded by twice the common edge
majorant. -/
theorem regularInverseGammaHorizontalDefect_norm_bound
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (familyEquality :
      family = zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    (K : ℝ)
    (carrierBound :
      ∀ x T : ℝ,
        x ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖zetaCompletedRegularInverseGammaContourCarrier f
            ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          K * (1 + ‖T‖) ^ (-(2 : ℤ)))
    (T : ℝ) :
    ‖zetaCompletedRegularInverseGammaHorizontalDefect f T‖ ≤
      (2 * K *
        (volume
          (Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)))).toReal) *
        (1 + ‖T‖) ^ (-(2 : ℤ)) :=
  let topEdge : ℂ :=
    ∫ x in Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)),
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + (T : ℂ) * Complex.I)
  let bottomEdge : ℂ :=
    ∫ x in Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)),
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  let stripVolume : ℝ :=
    (volume
      (Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)))).toReal
  let edgeMajorant : ℝ :=
    (K * (1 + ‖T‖) ^ (-(2 : ℤ))) * stripVolume
  let topBound : ‖topEdge‖ ≤ edgeMajorant :=
    regularInverseGamma_horizontalEdgeIntegral_norm_bound
      f family K carrierBound T
  let negativeHeightNorm : ‖-T‖ = ‖T‖ := norm_neg T
  let bottomRawBound :
      ‖bottomEdge‖ ≤
        (K * (1 + ‖-T‖) ^ (-(2 : ℤ))) * stripVolume :=
    regularInverseGamma_horizontalEdgeIntegral_norm_bound
      f family K carrierBound (-T)
  let bottomBound : ‖bottomEdge‖ ≤ edgeMajorant :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖bottomEdge‖ ≤
          (K * (1 + value) ^ (-(2 : ℤ))) * stripVolume)
      negativeHeightNorm bottomRawBound
  let differenceBound :
      ‖topEdge - bottomEdge‖ ≤ edgeMajorant + edgeMajorant :=
    (norm_sub_le topEdge bottomEdge).trans
      (add_le_add topBound bottomBound)
  let rotationNorm : ‖(-Complex.I : ℂ)‖ = 1 :=
    Eq.trans (norm_neg Complex.I) Complex.norm_I
  let defectEquality :
      zetaCompletedRegularInverseGammaHorizontalDefect f T =
        (-Complex.I) * (topEdge - bottomEdge) :=
    Eq.subst
      (motive := fun selectedFamily : ExplicitFormulaContourFamily =>
        zetaCompletedRegularInverseGammaHorizontalDefect f T =
          (-Complex.I) *
            ((∫ x in Set.Icc (0 : ℝ)
                (selectedFamily.c - (1 / 2 : ℝ)),
                zetaCompletedRegularInverseGammaContourCarrier f
                  ((x : ℂ) + (T : ℂ) * Complex.I)) -
              ∫ x in Set.Icc (0 : ℝ)
                (selectedFamily.c - (1 / 2 : ℝ)),
                zetaCompletedRegularInverseGammaContourCarrier f
                  ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))
      familyEquality.symm
      (Eq.refl (zetaCompletedRegularInverseGammaHorizontalDefect f T))
  let rotatedBound :
      ‖(-Complex.I) * (topEdge - bottomEdge)‖ ≤
        edgeMajorant + edgeMajorant :=
    let productNorm :
        ‖(-Complex.I) * (topEdge - bottomEdge)‖ =
          ‖(-Complex.I : ℂ)‖ * ‖topEdge - bottomEdge‖ :=
      norm_mul (-Complex.I) (topEdge - bottomEdge)
    let unitProduct :
        ‖(-Complex.I : ℂ)‖ * ‖topEdge - bottomEdge‖ =
          ‖topEdge - bottomEdge‖ :=
      Eq.trans
        (congrArg
          (fun value : ℝ => value * ‖topEdge - bottomEdge‖)
          rotationNorm)
        (one_mul ‖topEdge - bottomEdge‖)
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ edgeMajorant + edgeMajorant)
      (productNorm.trans unitProduct).symm differenceBound
  let majorantEquality :
      edgeMajorant + edgeMajorant =
        (2 * K * stripVolume) *
          (1 + ‖T‖) ^ (-(2 : ℤ)) :=
    let decay : ℝ := (1 + ‖T‖) ^ (-(2 : ℤ))
    let doubleEdge :
        edgeMajorant + edgeMajorant = 2 * edgeMajorant :=
      (two_mul edgeMajorant).symm
    let unfoldEdge :
        2 * edgeMajorant = 2 * ((K * decay) * stripVolume) :=
      rfl
    let reassociateLeft :
        2 * ((K * decay) * stripVolume) =
          (2 * K) * (decay * stripVolume) :=
      Eq.trans
        (congrArg (fun value : ℝ => 2 * value)
          (mul_assoc K decay stripVolume))
        (mul_assoc 2 K (decay * stripVolume)).symm
    let commuteDecay :
        (2 * K) * (decay * stripVolume) =
          (2 * K) * (stripVolume * decay) :=
      congrArg (fun value : ℝ => (2 * K) * value)
        (mul_comm decay stripVolume)
    let reassociateRight :
        (2 * K) * (stripVolume * decay) =
          (2 * K * stripVolume) * decay :=
      (mul_assoc (2 * K) stripVolume decay).symm
    Eq.trans doubleEdge
      (Eq.trans unfoldEdge
        (Eq.trans reassociateLeft
          (Eq.trans commuteDecay reassociateRight)))
  Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        (2 * K * stripVolume) * (1 + ‖T‖) ^ (-(2 : ℤ)))
    defectEquality.symm
    (rotatedBound.trans_eq majorantEquality)

/-- Uniform Paley-Wiener decay on the compact strip forces the two horizontal
inverse-Gamma edges to vanish. -/
theorem zetaCompletedRegularInverseGammaHorizontalDefect_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (zetaCompletedRegularInverseGammaHorizontalDefect f)
      Filter.atTop
      (𝓝 0) :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  match exists_regularInverseGammaContourCarrier_inverseQuadratic_bound
      f family with
  | ⟨K, KNonnegative, carrierBound⟩ =>
      let stripVolume : ℝ :=
        (volume
          (Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)))).toReal
      let constant : ℝ := 2 * K * stripVolume
      let defectBound :
          ∀ T : ℝ,
            ‖zetaCompletedRegularInverseGammaHorizontalDefect f T‖ ≤
              constant * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
        fun T =>
          regularInverseGammaHorizontalDefect_norm_bound
            f family (Eq.refl family) K carrierBound T
      let decayLimit :
          Filter.Tendsto
            (fun T : ℝ => (1 + ‖T‖) ^ (-(2 : ℤ)))
            Filter.atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_add_norm_pow_neg_atTop 1
      let majorantLimit :
          Filter.Tendsto
            (fun T : ℝ =>
              constant * (1 + ‖T‖) ^ (-(2 : ℤ)))
            Filter.atTop (𝓝 (0 : ℝ)) :=
        Eq.subst
          (motive := fun value : ℝ =>
            Filter.Tendsto
              (fun T : ℝ =>
                constant * (1 + ‖T‖) ^ (-(2 : ℤ)))
              Filter.atTop (𝓝 value))
          (mul_zero constant)
          (decayLimit.const_mul constant)
      squeeze_zero_norm'
        (Filter.Eventually.of_forall defectBound) majorantLimit

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
