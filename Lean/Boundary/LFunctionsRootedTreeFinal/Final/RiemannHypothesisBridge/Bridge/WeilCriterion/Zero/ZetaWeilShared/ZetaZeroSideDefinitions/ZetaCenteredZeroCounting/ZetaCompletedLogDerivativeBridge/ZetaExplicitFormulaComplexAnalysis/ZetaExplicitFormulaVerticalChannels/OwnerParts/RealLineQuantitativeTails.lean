import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RealLinePowerTailBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Quantitative tails on the real line

This file owns neutral real-line tail estimates used by vertical-channel
affine kernels.  The main theorem is independent of zeta: a complex-valued
function whose whole-line integral is zero and whose norm is dominated by a
fourth-order Japanese-bracket majorant has symmetric interval integrals of
size `O((1 + |T|)^{-2})`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

/-- The complement of a symmetric closed interval is the union of the two open
tails. -/
theorem realLine_compl_Icc_neg_eq_Iio_union_Ioi
    (T : ℝ) :
    (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
  ext x
  constructor
  · intro hx
    have hnot : ¬ (-T ≤ x ∧ x ≤ T) := hx
    match lt_or_ge x (-T) with
    | Or.inl hx_left =>
        exact Or.inl hx_left
    | Or.inr hx_not_left =>
        have hx_not_right : ¬ x ≤ T :=
          fun hx_right => hnot ⟨hx_not_left, hx_right⟩
        exact Or.inr (lt_of_not_ge hx_not_right)
  · intro hx
    match hx with
    | Or.inl hx_left =>
        exact Set.not_mem_Icc_of_lt hx_left
    | Or.inr hx_right =>
        exact Set.not_mem_Icc_of_gt hx_right

/-- Fourth-order Japanese brackets are nonnegative in the project `zpow`
normalization. -/
theorem realLine_one_add_norm_zpow_four_nonneg
    (t : ℝ) :
    0 ≤ (1 + ‖t‖) ^ (-(4 : ℤ)) :=
  realLineFourthOrderWeight_nonneg t

/-- Neutral analytic tail leaf: the fourth-order Japanese-bracket tail on the
complement of a symmetric interval is eventually inverse-quadratic.

This is the real-variable estimate
`∫_{|t| > T} (1 + |t|)^{-4} dt = O((1 + T)^{-3})`, weakened to the
inverse-quadratic form used by contour estimates. -/
theorem realLine_one_add_norm_zpow_four_compl_Icc_tail_eventually_le_inverseQuadratic :
    ∃ C : ℝ,
      0 < C ∧
        ∀ᶠ T in atTop,
          ∫ t in (Set.Icc (-T) T)ᶜ,
              (1 + ‖t‖) ^ (-(4 : ℤ))
            ≤ C * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  match realLineFourthOrderWeight_compl_Icc_tail_eventually_le_inverseQuadratic with
  | ⟨C, hC_pos, hC_eventual⟩ =>
      refine ⟨C, hC_pos, ?_⟩
      exact hC_eventual

/-- If the whole-line integral is zero, the integral over a measurable set is
the negative of the integral over its complement. -/
theorem realLine_setIntegral_eq_neg_compl_of_integral_zero
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (hzero : (∫ t : ℝ, φ t) = 0)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ t in s, φ t) = -∫ t in sᶜ, φ t := by
  have hsum :
      (∫ t in s, φ t) + (∫ t in sᶜ, φ t) = 0 :=
    Eq.trans
      (MeasureTheory.integral_add_compl (μ := volume) hs hφ_integrable)
      hzero
  exact eq_neg_of_add_eq_zero_left hsum

/-- Symmetric interval specialization of the zero-integral complement
decomposition. -/
theorem realLine_Icc_integral_eq_neg_compl_of_integral_zero
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (hzero : (∫ t : ℝ, φ t) = 0)
    (T : ℝ) :
    (∫ t in Set.Icc (-T) T, φ t) =
      -∫ t in (Set.Icc (-T) T)ᶜ, φ t :=
  realLine_setIntegral_eq_neg_compl_of_integral_zero
    φ hφ_integrable hzero (Set.Icc (-T) T) measurableSet_Icc

/-- The norm of a zero-integral function over a symmetric interval is bounded
by the integral of its norm over the complementary tails. -/
theorem realLine_Icc_integral_norm_le_compl_integral_norm_of_integral_zero
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (hzero : (∫ t : ℝ, φ t) = 0)
    (T : ℝ) :
    ‖∫ t in Set.Icc (-T) T, φ t‖
      ≤ ∫ t in (Set.Icc (-T) T)ᶜ, ‖φ t‖ := by
  have hcomp :
      (∫ t in Set.Icc (-T) T, φ t) =
        -∫ t in (Set.Icc (-T) T)ᶜ, φ t :=
    realLine_Icc_integral_eq_neg_compl_of_integral_zero
      φ hφ_integrable hzero T
  have hnorm :
      ‖∫ t in Set.Icc (-T) T, φ t‖ =
        ‖∫ t in (Set.Icc (-T) T)ᶜ, φ t‖ := by
    exact Eq.trans (congrArg norm hcomp) (norm_neg _)
  exact
    le_of_eq_of_le hnorm
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Icc (-T) T)ᶜ) φ)

/-- Arbitrary-value complement decomposition for a measurable set. -/
theorem realLine_setIntegral_sub_value_eq_neg_compl_of_integral_value
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (v : ℂ)
    (hvalue : (∫ t : ℝ, φ t) = v)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ t in s, φ t) - v = -∫ t in sᶜ, φ t := by
  let I : ℂ := ∫ t in s, φ t
  let J : ℂ := ∫ t in sᶜ, φ t
  have hsum : I + J = v :=
    Eq.trans
      (MeasureTheory.integral_add_compl (μ := volume) hs hφ_integrable)
      hvalue
  calc
    I - v = I - (I + J) := by
      exact congrArg (fun z : ℂ => I - z) hsum.symm
    _ = I + -(I + J) := by
      exact sub_eq_add_neg I (I + J)
    _ = I + (-I + -J) := by
      exact congrArg (fun z : ℂ => I + z) (neg_add I J)
    _ = (I + -I) + -J := by
      exact (add_assoc I (-I) (-J)).symm
    _ = 0 + -J := by
      exact congrArg (fun z : ℂ => z + -J) (add_right_neg I)
    _ = -J := by
      exact zero_add (-J)

/-- The norm of the interval integral minus the whole-line value is bounded by
the integral of the norm over the complementary tails. -/
theorem realLine_Icc_integral_sub_value_norm_le_compl_integral_norm_of_integral_value
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (v : ℂ)
    (hvalue : (∫ t : ℝ, φ t) = v)
    (T : ℝ) :
    ‖(∫ t in Set.Icc (-T) T, φ t) - v‖
      ≤ ∫ t in (Set.Icc (-T) T)ᶜ, ‖φ t‖ := by
  have hcomp :
      (∫ t in Set.Icc (-T) T, φ t) - v =
        -∫ t in (Set.Icc (-T) T)ᶜ, φ t :=
    realLine_setIntegral_sub_value_eq_neg_compl_of_integral_value
      φ hφ_integrable v hvalue (Set.Icc (-T) T) measurableSet_Icc
  have hnorm :
      ‖(∫ t in Set.Icc (-T) T, φ t) - v‖ =
        ‖∫ t in (Set.Icc (-T) T)ᶜ, φ t‖ := by
    exact Eq.trans (congrArg norm hcomp) (norm_neg _)
  exact
    le_of_eq_of_le hnorm
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Icc (-T) T)ᶜ) φ)

/-- Pointwise bridge from the project `zpow` convention for fourth-order
Japanese brackets to mathlib's `rpow` convention. -/
theorem realLine_one_add_norm_zpow_four_eq_rpow_four
    (t : ℝ) :
    (1 + ‖t‖) ^ (-(4 : ℤ)) =
      (1 + ‖t‖) ^ (-(4 : ℝ)) :=
  realLineFourthOrderWeight_eq_rpow t

/-- Integrability of the fourth-order Japanese-bracket majorant on the real
line. -/
theorem realLine_integrable_one_add_norm_zpow_four :
    Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(4 : ℤ)))
      (volume : Measure ℝ) := by
  have hbase :
      Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(4 : ℝ)))
        (volume : Measure ℝ) :=
    integrable_one_add_norm (E := ℝ) (μ := volume)
      (show (finrank ℝ ℝ : ℝ) < (4 : ℝ) from one_lt_ofNat)
  exact
    hbase.congr
      (Eventually.of_forall
        (fun t =>
          (realLine_one_add_norm_zpow_four_eq_rpow_four t).symm))

/-- Pointwise domination by a nonnegative fourth-order majorant integrates over
any measurable tail. -/
theorem realLine_setIntegral_norm_le_scaled_zpow_four_of_norm_le
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hmajorant :
      ∀ t : ℝ,
        ‖φ t‖ ≤ A * (1 + ‖t‖) ^ (-(4 : ℤ)))
    (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ t in s, ‖φ t‖
      ≤ A * ∫ t in s, (1 + ‖t‖) ^ (-(4 : ℤ)) := by
  let w : ℝ → ℝ := fun t => (1 + ‖t‖) ^ (-(4 : ℤ))
  have hnorm_integrable :
      IntegrableOn (fun t : ℝ => ‖φ t‖) s (volume : Measure ℝ) :=
    hφ_integrable.norm.integrableOn
  have hw_integrable :
      IntegrableOn w s (volume : Measure ℝ) :=
    realLine_integrable_one_add_norm_zpow_four.integrableOn
  have hAw_integrable :
      IntegrableOn (fun t : ℝ => A * w t) s (volume : Measure ℝ) :=
    hw_integrable.const_mul A
  have hmono :
      ∫ t in s, ‖φ t‖ ≤ ∫ t in s, A * w t :=
    MeasureTheory.setIntegral_mono_on
      hnorm_integrable hAw_integrable hs
      (fun t _ => hmajorant t)
  have hscale :
      (∫ t in s, A * w t) = A * ∫ t in s, w t :=
    MeasureTheory.integral_mul_left
      (μ := volume.restrict s) A w
  exact hmono.trans_eq hscale

/-- Complement decomposition and norm comparison for a zero-integral function
dominated by a fourth-order Japanese-bracket majorant.  This is the neutral
measure-theoretic bridge between a raw real tail estimate and a complex
interval-integral tail estimate. -/
theorem realLine_intervalIntegral_norm_le_scaled_compl_zpow_four_of_integral_zero_norm_le
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (hzero : (∫ t : ℝ, φ t) = 0)
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hmajorant :
      ∀ t : ℝ,
        ‖φ t‖ ≤ A * (1 + ‖t‖) ^ (-(4 : ℤ))) :
    ∀ T : ℝ,
      ‖∫ t in Set.Icc (-T) T, φ t‖
        ≤ A *
          ∫ t in (Set.Icc (-T) T)ᶜ,
            (1 + ‖t‖) ^ (-(4 : ℤ)) := by
  intro T
  have hnorm :
      ‖∫ t in Set.Icc (-T) T, φ t‖
        ≤ ∫ t in (Set.Icc (-T) T)ᶜ, ‖φ t‖ :=
    realLine_Icc_integral_norm_le_compl_integral_norm_of_integral_zero
      φ hφ_integrable hzero T
  have htail :
      ∫ t in (Set.Icc (-T) T)ᶜ, ‖φ t‖
        ≤ A *
          ∫ t in (Set.Icc (-T) T)ᶜ,
            (1 + ‖t‖) ^ (-(4 : ℤ)) :=
    realLine_setIntegral_norm_le_scaled_zpow_four_of_norm_le
      φ hφ_integrable A hA_nonneg hmajorant
      (Set.Icc (-T) T)ᶜ measurableSet_Icc.compl
  exact hnorm.trans htail

/-- Neutral analytic tail principle for complex-valued functions dominated by
a fourth-order Japanese-bracket majorant and with zero whole-line integral. -/
theorem realLine_intervalIntegral_eventually_inverseQuadratic_of_integral_zero_norm_le_zpow_four
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (hzero : (∫ t : ℝ, φ t) = 0)
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hmajorant :
      ∀ t : ℝ,
        ‖φ t‖ ≤ A * (1 + ‖t‖) ^ (-(4 : ℤ))) :
    ∃ M : ℝ,
      0 < M ∧
        ∀ᶠ T in atTop,
          ‖∫ t in Set.Icc (-T) T, φ t‖
            ≤ M * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  match realLine_one_add_norm_zpow_four_compl_Icc_tail_eventually_le_inverseQuadratic with
  | ⟨C, hCpos, hC⟩ =>
      let M : ℝ := A * C + 1
      have hMpos : 0 < M := by
        have hAC_nonneg : 0 ≤ A * C :=
          mul_nonneg hA_nonneg (le_of_lt hCpos)
        exact add_pos_of_nonneg_of_pos hAC_nonneg zero_lt_one
      have hscaled :
          ∀ᶠ T in atTop,
            A *
                ∫ t in (Set.Icc (-T) T)ᶜ,
                  (1 + ‖t‖) ^ (-(4 : ℤ))
              ≤ (A * C) * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
        hC.mono
          (fun T hT =>
            let q : ℝ := (1 + ‖T‖) ^ (-(2 : ℤ))
            have htail :
                ∫ t in (Set.Icc (-T) T)ᶜ,
                    (1 + ‖t‖) ^ (-(4 : ℤ))
                  ≤ C * q := hT
            have hmul :
                A *
                    ∫ t in (Set.Icc (-T) T)ᶜ,
                      (1 + ‖t‖) ^ (-(4 : ℤ))
                  ≤ A * (C * q) :=
              mul_le_mul_of_nonneg_left htail hA_nonneg
            hmul.trans_eq (mul_assoc A C q).symm)
      have hfinal :
          ∀ᶠ T in atTop,
            ‖∫ t in Set.Icc (-T) T, φ t‖
              ≤ M * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
        hscaled.mono
          (fun T hT =>
            let q : ℝ := (1 + ‖T‖) ^ (-(2 : ℤ))
            have hinterval :
                ‖∫ t in Set.Icc (-T) T, φ t‖
                  ≤ A *
                    ∫ t in (Set.Icc (-T) T)ᶜ,
                      (1 + ‖t‖) ^ (-(4 : ℤ)) :=
              realLine_intervalIntegral_norm_le_scaled_compl_zpow_four_of_integral_zero_norm_le
                φ hφ_integrable hzero A hA_nonneg hmajorant T
            have hMq :
                (A * C) * q ≤ M * q := by
              have hq_nonneg : 0 ≤ q :=
                zpow_nonneg (add_nonneg zero_le_one (norm_nonneg T)) (-(2 : ℤ))
              have hcoeff : A * C ≤ M := by
                exact le_add_of_nonneg_right zero_le_one
              exact mul_le_mul_of_nonneg_right hcoeff hq_nonneg
            hinterval.trans (hT.trans hMq))
      exact ⟨M, hMpos, hfinal⟩

/-- Neutral analytic tail principle around an arbitrary whole-line value.

This is the same complement-tail estimate as the zero-integral theorem, with
the interval integral compared to the recorded whole-line value. -/
theorem realLine_intervalIntegral_eventually_inverseQuadratic_of_integral_value_norm_le_zpow_four
    (φ : ℝ → ℂ)
    (hφ_integrable : Integrable φ (volume : Measure ℝ))
    (v : ℂ)
    (hvalue : (∫ t : ℝ, φ t) = v)
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hmajorant :
      ∀ t : ℝ,
        ‖φ t‖ ≤ A * (1 + ‖t‖) ^ (-(4 : ℤ))) :
    ∃ M : ℝ,
      0 < M ∧
        ∀ᶠ T in atTop,
          ‖(∫ t in Set.Icc (-T) T, φ t) - v‖
            ≤ M * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  match realLine_one_add_norm_zpow_four_compl_Icc_tail_eventually_le_inverseQuadratic with
  | ⟨C, hCpos, hC⟩ =>
      let M : ℝ := A * C + 1
      have hMpos : 0 < M := by
        have hAC_nonneg : 0 ≤ A * C :=
          mul_nonneg hA_nonneg (le_of_lt hCpos)
        exact add_pos_of_nonneg_of_pos hAC_nonneg zero_lt_one
      have hscaled :
          ∀ᶠ T in atTop,
            A *
                ∫ t in (Set.Icc (-T) T)ᶜ,
                  (1 + ‖t‖) ^ (-(4 : ℤ))
              ≤ (A * C) * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
        hC.mono
          (fun T hT =>
            let q : ℝ := (1 + ‖T‖) ^ (-(2 : ℤ))
            have htail :
                ∫ t in (Set.Icc (-T) T)ᶜ,
                    (1 + ‖t‖) ^ (-(4 : ℤ))
                  ≤ C * q := hT
            have hmul :
                A *
                    ∫ t in (Set.Icc (-T) T)ᶜ,
                      (1 + ‖t‖) ^ (-(4 : ℤ))
                  ≤ A * (C * q) :=
              mul_le_mul_of_nonneg_left htail hA_nonneg
            hmul.trans_eq (mul_assoc A C q).symm)
      have hfinal :
          ∀ᶠ T in atTop,
            ‖(∫ t in Set.Icc (-T) T, φ t) - v‖
              ≤ M * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
        hscaled.mono
          (fun T hT =>
            let q : ℝ := (1 + ‖T‖) ^ (-(2 : ℤ))
            have hinterval :
                ‖(∫ t in Set.Icc (-T) T, φ t) - v‖
                  ≤ A *
                    ∫ t in (Set.Icc (-T) T)ᶜ,
                      (1 + ‖t‖) ^ (-(4 : ℤ)) := by
              have hnorm :
                  ‖(∫ t in Set.Icc (-T) T, φ t) - v‖
                    ≤ ∫ t in (Set.Icc (-T) T)ᶜ, ‖φ t‖ :=
                realLine_Icc_integral_sub_value_norm_le_compl_integral_norm_of_integral_value
                  φ hφ_integrable v hvalue T
              have htail :
                  ∫ t in (Set.Icc (-T) T)ᶜ, ‖φ t‖
                    ≤ A *
                      ∫ t in (Set.Icc (-T) T)ᶜ,
                        (1 + ‖t‖) ^ (-(4 : ℤ)) :=
                realLine_setIntegral_norm_le_scaled_zpow_four_of_norm_le
                  φ hφ_integrable A hA_nonneg hmajorant
                  (Set.Icc (-T) T)ᶜ measurableSet_Icc.compl
              exact hnorm.trans htail
            have hMq :
                (A * C) * q ≤ M * q := by
              have hq_nonneg : 0 ≤ q :=
                zpow_nonneg (add_nonneg zero_le_one (norm_nonneg T)) (-(2 : ℤ))
              have hcoeff : A * C ≤ M := by
                exact le_add_of_nonneg_right zero_le_one
              exact mul_le_mul_of_nonneg_right hcoeff hq_nonneg
            hinterval.trans (hT.trans hMq))
      exact ⟨M, hMpos, hfinal⟩

end
end LFunctions
end Boundary
