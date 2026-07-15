import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.UnitBlockCombinedPhase

/-!
# Logarithmic derivative amplitude on a unit block

After the zero-boundary Bernoulli integration by parts, the centered quadratic
primitive is multiplied by the logarithmic derivative amplitude
`(t/(a+u))(-i)`.  This file owns that amplitude and its post-cutoff size.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Complex logarithmic derivative amplitude in unit-block coordinates. -/
noncomputable def boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) : ℂ :=
  ((t / ((a : ℝ) + u) : ℝ) : ℂ) * (-Complex.I)

/-- Derivative of the complex logarithmic derivative amplitude. -/
noncomputable def boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) : ℂ :=
  ((-(t / (((a : ℝ) + u) ^ (2 : ℕ))) : ℝ) : ℂ) *
    (-Complex.I)

/-- The norm of the complex unit-block amplitude is the absolute logarithmic
speed. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) :
    ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u‖ =
      |t / ((a : ℝ) + u)| := by
  let r : ℝ := t / ((a : ℝ) + u)
  have hreal : ‖(r : ℂ)‖ = ‖r‖ :=
    Complex.norm_real r
  have hnegativeI : ‖-Complex.I‖ = 1 :=
    Eq.trans (norm_neg Complex.I) Complex.norm_I
  have hrealAbs : ‖r‖ = |r| :=
    Real.norm_eq_abs r
  exact Eq.trans
    (norm_mul (r : ℂ) (-Complex.I))
    (Eq.trans
      (congrArg₂ Mul.mul hreal hnegativeI)
      (Eq.trans (mul_one ‖r‖) hrealAbs))

/-- Past the canonical cutoff, the complex logarithmic derivative amplitude
has norm at most one throughout every unit block. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_le_one
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u‖ ≤ 1 := by
  have hx :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_postCutoff_le_coordinate
      t ha hu
  have hspeed : |t / ((a : ℝ) + u)| ≤ 1 :=
    boundaryLineOnePointRealParam_postCutoff_abs_div_le_one t hx
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 1)
    (norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
      t a u).symm
    hspeed

/-- The declared complex amplitude derivative is the actual derivative on the
positive part of a unit block. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
    (t : ℝ)
    (a : ℕ)
    {u : ℝ}
    (hx : 0 < (a : ℝ) + u) :
    HasDerivAt
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
        t a u)
      u := by
  let x : ℝ := (a : ℝ) + u
  let shifted : ℝ → ℝ := fun v => (a : ℝ) + v
  have hshiftRaw : HasDerivAt shifted (0 + 1) u :=
    (hasDerivAt_const u (a : ℝ)).add (hasDerivAt_id u)
  have hshift : HasDerivAt shifted 1 u :=
    hshiftRaw.congr_deriv (zero_add 1)
  have hinverse :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ (2 : ℕ))⁻¹) x :=
    hasDerivAt_inv (ne_of_gt hx)
  have hscaledRaw :
      HasDerivAt
        (fun y : ℝ => t * y⁻¹)
        (t * (-(x ^ (2 : ℕ))⁻¹))
        x :=
    hinverse.const_mul t
  have hfunctionReal :
      (fun y : ℝ => t * y⁻¹) = (fun y : ℝ => t / y) := by
    funext y
    exact (div_eq_mul_inv t y).symm
  have hcoefficientReal :
      t * (-(x ^ (2 : ℕ))⁻¹) = -(t / x ^ (2 : ℕ)) := by
    exact Eq.trans
      (mul_neg t (x ^ (2 : ℕ))⁻¹)
      (congrArg Neg.neg (div_eq_mul_inv t (x ^ (2 : ℕ))).symm)
  have hscaled :
      HasDerivAt
        (fun y : ℝ => t / y)
        (-(t / x ^ (2 : ℕ)))
        x :=
    Eq.subst
      (motive := fun f : ℝ → ℝ =>
        HasDerivAt f (-(t / x ^ (2 : ℕ))) x)
      hfunctionReal
      (hscaledRaw.congr_deriv hcoefficientReal)
  have hcomposedRaw :
      HasDerivAt
        (fun v : ℝ => t / ((a : ℝ) + v))
        ((-(t / x ^ (2 : ℕ))) * 1)
        u :=
    hscaled.comp u hshift
  have hcomposed :
      HasDerivAt
        (fun v : ℝ => t / ((a : ℝ) + v))
        (-(t / (((a : ℝ) + u) ^ (2 : ℕ))))
        u :=
    hcomposedRaw.congr_deriv (mul_one _)
  have hcomplex :
      HasDerivAt
        (fun v : ℝ => ((t / ((a : ℝ) + v) : ℝ) : ℂ))
        ((-(t / (((a : ℝ) + u) ^ (2 : ℕ))) : ℝ) : ℂ)
        u :=
    hcomposed.ofReal_comp
  exact hcomplex.mul_const (-Complex.I)

/-- The derivative amplitude has the expected inverse-square norm. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) :
    ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
        t a u‖ =
      |t / (((a : ℝ) + u) ^ (2 : ℕ))| := by
  let r : ℝ := -(t / (((a : ℝ) + u) ^ (2 : ℕ)))
  have hreal : ‖(r : ℂ)‖ = ‖r‖ :=
    Complex.norm_real r
  have hnegativeI : ‖-Complex.I‖ = 1 :=
    Eq.trans (norm_neg Complex.I) Complex.norm_I
  have hrealAbs : ‖r‖ = |r| :=
    Real.norm_eq_abs r
  have habsNeg :
      |-(t / (((a : ℝ) + u) ^ (2 : ℕ)))| =
        |t / (((a : ℝ) + u) ^ (2 : ℕ))| :=
    abs_neg (t / (((a : ℝ) + u) ^ (2 : ℕ)))
  exact Eq.trans
    (norm_mul (r : ℂ) (-Complex.I))
    (Eq.trans
      (congrArg₂ Mul.mul hreal hnegativeI)
      (Eq.trans
        (mul_one ‖r‖)
        (Eq.trans hrealAbs habsNeg)))

/-- On the positive translated half-line, the amplitude derivative has the
exact inverse-square majorant needed for global integration. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative_eq_inverseSquare
    (t : ℝ)
    (a : ℕ)
    {u : ℝ}
    (hx : 0 < (a : ℝ) + u) :
    ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
        t a u‖ =
      ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) := by
  have habs_t : |t| = ‖t‖ :=
    (Real.norm_eq_abs t).symm
  have hsquare_pos : 0 < ((a : ℝ) + u) ^ (2 : ℕ) :=
    sq_pos_of_pos hx
  have habs_square :
      |((a : ℝ) + u) ^ (2 : ℕ)| =
        ((a : ℝ) + u) ^ (2 : ℕ) :=
    abs_of_pos hsquare_pos
  have habs_quotient :
      |t / (((a : ℝ) + u) ^ (2 : ℕ))| =
        ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) :=
    Eq.trans
      (abs_div t (((a : ℝ) + u) ^ (2 : ℕ)))
      (congrArg₂ Div.div habs_t habs_square)
  exact Eq.trans
    (norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
      t a u)
    habs_quotient

/-- On a post-cutoff block, the amplitude derivative is bounded by the
inverse square of the block's left endpoint. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative_le
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
        t a u‖ ≤
      ‖t‖ / ((a : ℝ) ^ (2 : ℕ)) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_fourier_cutoff_pos t
  have ha_nat_pos : 0 < a :=
    lt_of_lt_of_le hcutoff_pos ha
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr ha_nat_pos
  have hx_pos : 0 < (a : ℝ) + u :=
    lt_of_lt_of_le ha_pos (le_add_of_nonneg_right hu)
  have ha_le_x : (a : ℝ) ≤ (a : ℝ) + u :=
    le_add_of_nonneg_right hu
  have hsquare :
      (a : ℝ) ^ (2 : ℕ) ≤ ((a : ℝ) + u) ^ (2 : ℕ) := by
    exact sq_le_sq.mpr
      (calc
        |(a : ℝ)| = (a : ℝ) := abs_of_pos ha_pos
        _ ≤ (a : ℝ) + u := ha_le_x
        _ = |(a : ℝ) + u| := (abs_of_pos hx_pos).symm)
  have hquotient :
      ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) ≤
        ‖t‖ / ((a : ℝ) ^ (2 : ℕ)) :=
    div_le_div_of_nonneg_left
      (norm_nonneg t)
      (sq_pos_of_pos ha_pos)
      hsquare
  have habs_t : |t| = ‖t‖ :=
    (Real.norm_eq_abs t).symm
  have habs_denominator :
      |((a : ℝ) + u) ^ (2 : ℕ)| =
        ((a : ℝ) + u) ^ (2 : ℕ) :=
    abs_of_pos (sq_pos_of_pos hx_pos)
  have habs_quotient :
      |t / (((a : ℝ) + u) ^ (2 : ℕ))| =
        ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) := by
    exact Eq.trans
      (abs_div t (((a : ℝ) + u) ^ (2 : ℕ)))
      (congrArg₂ Div.div habs_t habs_denominator)
  exact le_trans
    (le_of_eq
      (Eq.trans
        (norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
          t a u)
        habs_quotient))
    hquotient

end
end LFunctions
end Boundary
