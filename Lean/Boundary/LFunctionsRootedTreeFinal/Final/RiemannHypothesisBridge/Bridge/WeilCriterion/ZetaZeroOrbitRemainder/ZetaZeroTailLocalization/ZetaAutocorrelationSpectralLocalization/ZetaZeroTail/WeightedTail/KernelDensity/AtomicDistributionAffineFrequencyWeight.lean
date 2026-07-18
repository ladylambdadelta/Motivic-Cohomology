import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffOscillatoryDecay

/-!
# Affine frequency weights

A positive affine change of frequency preserves polynomial decay.  The proofs
below expose the height comparison and the reciprocal-power transport as
separate owner lemmas.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The explicit height factor for a positive affine frequency change. -/
noncomputable def affineFrequencyHeightFactor
    (shift scale : ℝ) : ℝ :=
  1 + |shift| + scale⁻¹

/-- The affine frequency height factor is positive at positive scale. -/
theorem affineFrequencyHeightFactor_pos
    (shift scale : ℝ)
    (hscale : 0 < scale) :
    0 < affineFrequencyHeightFactor shift scale := by
  have hinverseNonnegative : 0 ≤ scale⁻¹ :=
    le_of_lt (inv_pos.mpr hscale)
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg shift))
    hinverseNonnegative

/-- Absolute displacement is recovered from the scaled affine frequency. -/
theorem inverse_mul_abs_scaledDisplacement
    (shift scale y : ℝ)
    (hscale : 0 < scale) :
    scale⁻¹ * |scale * (y - shift)| = |y - shift| := by
  have hscaleAbsolute : |scale| = scale :=
    abs_of_pos hscale
  have habsoluteProduct :
      |scale * (y - shift)| = scale * |y - shift| :=
    Eq.trans
      (abs_mul scale (y - shift))
      (congrArg
        (fun value : ℝ => value * |y - shift|)
        hscaleAbsolute)
  have hscaleNonzero : scale ≠ 0 :=
    ne_of_gt hscale
  exact Eq.trans
    (congrArg (fun value : ℝ => scale⁻¹ * value)
      habsoluteProduct)
    (Eq.trans
      (mul_assoc scale⁻¹ scale |y - shift|).symm
      (Eq.trans
        (congrArg
          (fun value : ℝ => value * |y - shift|)
          (inv_mul_cancel₀ hscaleNonzero))
        (one_mul |y - shift|)))

/-- Canonical height comparison under a positive affine frequency change. -/
theorem one_add_abs_le_affineFrequencyHeightFactor_mul
    (shift scale y : ℝ)
    (hscale : 0 < scale) :
    1 + |y| ≤
      affineFrequencyHeightFactor shift scale *
        (1 + |scale * (y - shift)|) := by
  let displacement : ℝ := y - shift
  let frequencyAbsolute : ℝ := |scale * displacement|
  let factor : ℝ := affineFrequencyHeightFactor shift scale
  have hyDecomposition : y = displacement + shift :=
    (sub_add_cancel y shift).symm
  have habsoluteY : |y| ≤ |displacement| + |shift| :=
    Eq.subst
      (motive := fun value : ℝ => |value| ≤ |displacement| + |shift|)
      hyDecomposition.symm
      (abs_add_le displacement shift)
  have hdisplacement :
      |displacement| = scale⁻¹ * frequencyAbsolute :=
    (inverse_mul_abs_scaledDisplacement shift scale y hscale).symm
  have hleft :
      1 + |y| ≤
        (1 + |shift|) + scale⁻¹ * frequencyAbsolute := by
    have honeAdded :
        1 + |y| ≤ 1 + (|displacement| + |shift|) :=
      add_le_add_left habsoluteY 1
    have hreorder :
        1 + (|displacement| + |shift|) =
          (1 + |shift|) + |displacement| := by
      exact Eq.trans
        (congrArg
          (fun value : ℝ => 1 + value)
          (add_comm |displacement| |shift|))
        (add_assoc 1 |shift| |displacement|).symm
    exact le_trans honeAdded
      (Eq.subst
        (motive := fun right : ℝ =>
          1 + (|displacement| + |shift|) ≤ right)
        (Eq.trans hreorder
          (congrArg
            (fun value : ℝ => (1 + |shift|) + value)
            hdisplacement))
        (le_refl (1 + (|displacement| + |shift|))))
  have hinverseNonnegative : 0 ≤ scale⁻¹ :=
    le_of_lt (inv_pos.mpr hscale)
  have hshiftHeightNonnegative : 0 ≤ 1 + |shift| :=
    add_nonneg zero_le_one (abs_nonneg shift)
  have hfrequencyNonnegative : 0 ≤ frequencyAbsolute :=
    abs_nonneg (scale * displacement)
  have hshiftPart : 1 + |shift| ≤ factor :=
    le_add_of_nonneg_right hinverseNonnegative
  have hinversePart : scale⁻¹ ≤ factor :=
    le_add_of_nonneg_left hshiftHeightNonnegative
  have hfrequencyPart :
      scale⁻¹ * frequencyAbsolute ≤ factor * frequencyAbsolute :=
    mul_le_mul_of_nonneg_right hinversePart hfrequencyNonnegative
  have hsum :
      (1 + |shift|) + scale⁻¹ * frequencyAbsolute ≤
        factor + factor * frequencyAbsolute :=
    add_le_add hshiftPart hfrequencyPart
  have hproduct :
      factor * (1 + frequencyAbsolute) =
        factor + factor * frequencyAbsolute :=
    Eq.trans
      (mul_add factor 1 frequencyAbsolute)
      (congrArg
        (fun value : ℝ => value + factor * frequencyAbsolute)
        (mul_one factor))
  exact le_trans hleft
    (Eq.subst
      (motive := fun right : ℝ =>
        (1 + |shift|) + scale⁻¹ * frequencyAbsolute ≤ right)
      hproduct.symm
      hsum)

/-- Natural powers preserve an inequality between positive real heights. -/
theorem positiveHeight_naturalPower_mono
    (heightSource heightTarget : ℝ)
    (degree : ℕ)
    (hsource : 0 < heightSource)
    (hheight : heightSource ≤ heightTarget) :
    heightSource ^ degree ≤ heightTarget ^ degree :=
  pow_le_pow_left₀ (le_of_lt hsource) hheight degree

/-- A multiplicative comparison of positive heights expands into the
corresponding comparison of natural powers. -/
theorem heightPower_le_factorPow_mul_heightPower
    (heightSource heightTarget factor : ℝ)
    (degree : ℕ)
    (hsource : 0 < heightSource)
    (hheight : heightSource ≤ factor * heightTarget) :
    heightSource ^ degree ≤
      factor ^ degree * heightTarget ^ degree := by
  have hproductPower :
      heightSource ^ degree ≤ (factor * heightTarget) ^ degree :=
    positiveHeight_naturalPower_mono
      heightSource (factor * heightTarget) degree hsource hheight
  exact Eq.subst
    (motive := fun right : ℝ => heightSource ^ degree ≤ right)
    (mul_pow factor heightTarget degree)
    hproductPower

/-- A positive multiplicative height comparison transports reciprocal natural
powers in the opposite direction. -/
theorem negativePower_le_factorPow_mul_negativePower_of_height_le
    (heightSource heightTarget factor : ℝ)
    (degree : ℕ)
    (hsource : 0 < heightSource)
    (htarget : 0 < heightTarget)
    (hfactor : 0 < factor)
    (hheight : heightSource ≤ factor * heightTarget) :
    heightTarget ^ (-(degree : ℤ)) ≤
      factor ^ degree * heightSource ^ (-(degree : ℤ)) := by
  have hpower :
      heightSource ^ degree ≤
        factor ^ degree * heightTarget ^ degree :=
    heightPower_le_factorPow_mul_heightPower
      heightSource heightTarget factor degree hsource hheight
  have hsourcePowerPositive : 0 < heightSource ^ degree :=
    pow_pos hsource degree
  have htargetPowerPositive : 0 < heightTarget ^ degree :=
    pow_pos htarget degree
  have hdivision :
      1 / heightTarget ^ degree ≤
        factor ^ degree / heightSource ^ degree :=
    (div_le_div_iff₀ htargetPowerPositive hsourcePowerPositive).mpr
      (Eq.subst
        (motive := fun left : ℝ =>
          left ≤ factor ^ degree * heightTarget ^ degree)
        (one_mul (heightSource ^ degree)).symm
        hpower)
  have htargetNegative :
      heightTarget ^ (-(degree : ℤ)) =
        1 / heightTarget ^ degree := by
    exact Eq.trans
      (zpow_neg heightTarget (degree : ℤ))
      (Eq.trans
        (congrArg Inv.inv (zpow_natCast heightTarget degree))
        (one_div (heightTarget ^ degree)).symm)
  have hsourceNegative :
      factor ^ degree * heightSource ^ (-(degree : ℤ)) =
        factor ^ degree / heightSource ^ degree := by
    exact Eq.trans
      (congrArg
        (fun value : ℝ => factor ^ degree * value)
        (Eq.trans
          (zpow_neg heightSource (degree : ℤ))
          (congrArg Inv.inv (zpow_natCast heightSource degree))))
      (div_eq_mul_inv (factor ^ degree) (heightSource ^ degree)).symm
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ factor ^ degree * heightSource ^ (-(degree : ℤ)))
    htargetNegative.symm
    (Eq.subst
      (motive := fun right : ℝ =>
        1 / heightTarget ^ degree ≤ right)
      hsourceNegative.symm
      hdivision)

/-- Reciprocal affine-frequency weights are controlled by the original
canonical height weight. -/
theorem affineFrequency_negativePower_le
    (shift scale y : ℝ)
    (hscale : 0 < scale)
    (degree : ℕ) :
    (1 + |scale * (y - shift)|) ^ (-(degree : ℤ)) ≤
      affineFrequencyHeightFactor shift scale ^ degree *
        (1 + |y|) ^ (-(degree : ℤ)) := by
  exact negativePower_le_factorPow_mul_negativePower_of_height_le
    (1 + |y|)
    (1 + |scale * (y - shift)|)
    (affineFrequencyHeightFactor shift scale)
    degree
    (add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg y))
    (add_pos_of_pos_of_nonneg zero_lt_one
      (abs_nonneg (scale * (y - shift))))
    (affineFrequencyHeightFactor_pos shift scale hscale)
    (one_add_abs_le_affineFrequencyHeightFactor_mul shift scale y hscale)

/-- If a positive height is bounded by a positive constant, the corresponding
negative power has enough mass to absorb one. -/
theorem one_le_factorPow_mul_negativePower_of_height_le
    (height factor : ℝ)
    (degree : ℕ)
    (hheightPositive : 0 < height)
    (hfactorPositive : 0 < factor)
    (hheight : height ≤ factor) :
    1 ≤ factor ^ degree * height ^ (-(degree : ℤ)) := by
  have hpower : height ^ degree ≤ factor ^ degree :=
    positiveHeight_naturalPower_mono
      height factor degree hheightPositive hheight
  have hheightPowerPositive : 0 < height ^ degree :=
    pow_pos hheightPositive degree
  have hdivision : 1 ≤ factor ^ degree / height ^ degree :=
    (le_div_iff₀ hheightPowerPositive).mpr
      (Eq.subst
        (motive := fun left : ℝ => left ≤ factor ^ degree)
        (one_mul (height ^ degree)).symm
        hpower)
  have hnegative :
      factor ^ degree * height ^ (-(degree : ℤ)) =
        factor ^ degree / height ^ degree := by
    exact Eq.trans
      (congrArg
        (fun value : ℝ => factor ^ degree * value)
        (Eq.trans
          (zpow_neg height (degree : ℤ))
          (congrArg Inv.inv (zpow_natCast height degree))))
      (div_eq_mul_inv (factor ^ degree) (height ^ degree)).symm
  exact Eq.subst
    (motive := fun right : ℝ => 1 ≤ right)
    hnegative.symm
    hdivision

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
