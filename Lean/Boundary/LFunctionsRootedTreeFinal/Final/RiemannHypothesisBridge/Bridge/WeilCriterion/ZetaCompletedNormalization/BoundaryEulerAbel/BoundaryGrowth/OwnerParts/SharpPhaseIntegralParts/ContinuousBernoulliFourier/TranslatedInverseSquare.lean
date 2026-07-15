import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ModewiseGlobalIntegrationByParts

/-!
# Translated inverse-square mass after the canonical cutoff

This file evaluates the scalar majorant left by global modewise integration by
parts.  Its mass is bounded independently of the length of the upper interval.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The elementary antiderivative of the translated inverse-square density. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_translatedInverseSquareAntiderivative
    (t : ℝ)
    (a : ℕ)
    {u : ℝ}
    (hx : 0 < (a : ℝ) + u) :
    HasDerivAt
      (fun v : ℝ => -(‖t‖ * (((a : ℝ) + v)⁻¹)))
      (‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)))
      u := by
  have hshiftRaw :
      HasDerivAt (fun v : ℝ => (a : ℝ) + v) (0 + 1) u :=
    (hasDerivAt_const u (a : ℝ)).add (hasDerivAt_id u)
  have hshift :
      HasDerivAt (fun v : ℝ => (a : ℝ) + v) 1 u :=
    hshiftRaw.congr_deriv (zero_add 1)
  have hinverseBase :
      HasDerivAt (fun x : ℝ => x⁻¹)
        (-(((a : ℝ) + u) ^ (2 : ℕ))⁻¹) ((a : ℝ) + u) :=
    hasDerivAt_inv (ne_of_gt hx)
  have hinverseRaw :
      HasDerivAt (fun v : ℝ => (((a : ℝ) + v)⁻¹))
        ((-(((a : ℝ) + u) ^ (2 : ℕ))⁻¹) * 1) u :=
    hinverseBase.comp u hshift
  have hinverse :
      HasDerivAt (fun v : ℝ => (((a : ℝ) + v)⁻¹))
        (-(((a : ℝ) + u) ^ (2 : ℕ))⁻¹) u :=
    hinverseRaw.congr_deriv (mul_one _)
  have hscaled := (hinverse.const_mul ‖t‖).neg
  have hcoefficient :
      -(‖t‖ * -(((a : ℝ) + u) ^ (2 : ℕ))⁻¹) =
        ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) := by
    exact Eq.trans
      (congrArg Neg.neg
        (mul_neg ‖t‖ ((((a : ℝ) + u) ^ (2 : ℕ))⁻¹)))
      (Eq.trans
        (neg_neg (‖t‖ * ((((a : ℝ) + u) ^ (2 : ℕ))⁻¹)))
        (div_eq_mul_inv ‖t‖ (((a : ℝ) + u) ^ (2 : ℕ))).symm)
  exact hscaled.congr_deriv hcoefficient

/-- The translated inverse-square density is interval-integrable on every
finite positive translated interval. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_translatedInverseSquare
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    IntervalIntegrable
      (fun u : ℝ => ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)))
      volume 0 L := by
  have hcontinuous :
      ContinuousOn
        (fun u : ℝ => ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)))
        (Set.uIcc 0 L) := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) L :=
      Eq.subst (motive := fun s : Set ℝ => u ∈ s) (Set.uIcc_of_le hL) hu
    have hx : 0 < (a : ℝ) + u :=
      boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha huIcc.1
    have hshift : ContinuousAt (fun v : ℝ => (a : ℝ) + v) u :=
      continuousAt_const.add continuousAt_id
    exact
      (continuousAt_const.div (hshift.pow 2)
        (pow_ne_zero 2 (ne_of_gt hx))).continuousWithinAt
  exact hcontinuous.intervalIntegrable

/-- The translated inverse-square integral is the endpoint difference of its
explicit antiderivative. -/
theorem intervalIntegral_boundaryLineOnePointRealParam_translatedInverseSquare_eq
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ u in (0 : ℝ)..L,
        ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ))) =
      -(‖t‖ * (((a : ℝ) + L)⁻¹)) -
        (-(‖t‖ * (((a : ℝ) + 0)⁻¹))) := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu =>
        hasDerivAt_boundaryLineOnePointRealParam_translatedInverseSquareAntiderivative
          t a
          (boundaryLineOnePointRealParam_unitBlock_coordinate_pos
            t ha
            ((Eq.subst (motive := fun s : Set ℝ => u ∈ s)
              (Set.uIcc_of_le hL) hu).1)))
      (intervalIntegrable_boundaryLineOnePointRealParam_translatedInverseSquare
        t ha hL)

/-- The total translated inverse-square mass after the canonical cutoff is at
most one. -/
theorem intervalIntegral_boundaryLineOnePointRealParam_translatedInverseSquare_le_one
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ u in (0 : ℝ)..L,
        ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ))) ≤ 1 := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_fourier_cutoff_pos t
  have ha_nat_pos : 0 < a :=
    lt_of_lt_of_le hcutoff_pos ha
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr ha_nat_pos
  have haL_pos : (0 : ℝ) < (a : ℝ) + L :=
    lt_of_lt_of_le ha_pos (le_add_of_nonneg_right hL)
  have hnorm_le_a : ‖t‖ ≤ (a : ℝ) :=
    le_trans
      (le_trans (le_add_of_nonneg_left zero_le_one)
        (boundaryLineOnePointRealParam_fourier_one_add_norm_le_cutoff t))
      (Nat.cast_le.mpr ha)
  have hratio : ‖t‖ / (a : ℝ) ≤ 1 :=
    (div_le_one₀ ha_pos).mpr hnorm_le_a
  have hupper_nonneg : 0 ≤ ‖t‖ / ((a : ℝ) + L) :=
    div_nonneg (norm_nonneg t) (le_of_lt haL_pos)
  have hendpoint_le :
      ‖t‖ / (a : ℝ) - ‖t‖ / ((a : ℝ) + L) ≤ ‖t‖ / (a : ℝ) :=
    sub_le_self _ hupper_nonneg
  have hendpointIdentity :
      -(‖t‖ * (((a : ℝ) + L)⁻¹)) -
          (-(‖t‖ * (((a : ℝ) + 0)⁻¹))) =
        ‖t‖ / (a : ℝ) - ‖t‖ / ((a : ℝ) + L) := by
    calc
      -(‖t‖ * (((a : ℝ) + L)⁻¹)) -
          (-(‖t‖ * (((a : ℝ) + 0)⁻¹))) =
          ‖t‖ * (((a : ℝ) + 0)⁻¹) -
            ‖t‖ * (((a : ℝ) + L)⁻¹) := by
        exact Eq.trans
          (sub_neg_eq_add _ _)
          (Eq.trans
            (add_comm _ _)
            (sub_eq_add_neg _ _).symm)
      _ = ‖t‖ / (a : ℝ) - ‖t‖ / ((a : ℝ) + L) := by
        exact congrArg₂ Sub.sub
          (Eq.trans
            (congrArg (fun x : ℝ => ‖t‖ * x)
              (congrArg Inv.inv (add_zero (a : ℝ))))
            (div_eq_mul_inv ‖t‖ (a : ℝ)).symm)
          (div_eq_mul_inv ‖t‖ ((a : ℝ) + L)).symm
  have hintegral :=
    intervalIntegral_boundaryLineOnePointRealParam_translatedInverseSquare_eq
      t ha hL
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 1)
    hintegral.symm
    (Eq.subst
      (motive := fun value : ℝ => value ≤ 1)
      hendpointIdentity.symm
      (le_trans hendpoint_le hratio))

end
end LFunctions
end Boundary
