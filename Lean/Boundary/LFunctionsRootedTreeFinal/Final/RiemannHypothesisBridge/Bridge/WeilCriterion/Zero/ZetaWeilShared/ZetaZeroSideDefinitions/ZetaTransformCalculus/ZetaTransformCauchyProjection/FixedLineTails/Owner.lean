import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.FixedLineKernel.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

theorem fixedRightLine_fourierCauchy_multiplierIntegrand_inverseCubicDecay
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ t : ℝ,
          ‖(-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
            ≤ C * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
  exact
    Exists.elim
      (fixedRightLine_weightedKernel_fourierIntegral_inverseQuadraticDecay
        K hK_cont hK_compact hK_smooth c hc)
      (fun B hB =>
        Exists.elim
          (fixedRightLine_cauchyMultiplier_norm_inverseLinearBound c hc)
          (fun D hD =>
            fixedRightLine_cauchyMultiplier_times_fourierIntegral_inverseCubicBound
              (fun t : ℝ =>
                ∫ x : ℝ,
                  K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
              (fun t : ℝ =>
                -1 / (((c : ℂ) + t * Complex.I) - 1))
              B D hB.left hD.left hB.right hD.right))

/-- A cofinal height schedule is eventually nonnegative. -/
theorem cofinalHeight_eventually_nonnegative
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∀ᶠ u in atTop, 0 ≤ height u := by
  exact hcofinal.eventually_ge_atTop 0

/-- A cofinal height schedule sends the Japanese bracket to infinity. -/
theorem cofinalHeight_one_add_norm_tendsto_atTop
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    Tendsto (fun u : ℝ => (1 + ‖height u‖ : ℝ)) atTop atTop :=
  tendsto_atTop.2
    (fun A : ℝ =>
      (hcofinal.eventually_ge_atTop A).mono
        (fun u hu =>
          le_trans hu
            (le_trans
              (Real.le_norm_self (height u))
              (le_add_of_nonneg_left zero_le_one))))

/-- Inverse-square decay along a cofinal height schedule tends to zero. -/
theorem cofinalHeight_one_add_norm_inverseQuadratic_tendsto_zero
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    Tendsto
      (fun u : ℝ => (1 + ‖height u‖) ^ (-(2 : ℤ)) : ℝ)
      atTop
      (𝓝 0) :=
  (tendsto_zpow_atTop_zero (show (-(2 : ℤ)) < 0 by exact Int.negSucc_lt_zero 1)).comp
    (cofinalHeight_one_add_norm_tendsto_atTop height hcofinal)

/-- On a nonnegative tail, the inverse-cubic norm weight is the translated
real-power weight. -/
theorem real_inverseCubic_rightTail_value_eq_shifted_rpow
    (T t : ℝ) (hT : 0 ≤ T) (ht : t ∈ Set.Ici T) :
    (1 + ‖t‖) ^ (-(3 : ℤ)) = (t + 1) ^ (-(3 : ℝ)) := by
  have ht_nonneg : 0 ≤ t :=
    le_trans hT ht
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  calc
    (1 + ‖t‖) ^ (-(3 : ℤ))
        = (1 + t) ^ (-(3 : ℤ)) := by
          exact congrArg (fun x : ℝ => x ^ (-(3 : ℤ)))
            (congrArg (fun x : ℝ => 1 + x) hnorm)
    _ = (1 + t) ^ (-(3 : ℝ)) := by
          exact (Real.rpow_intCast (1 + t) (-(3 : ℤ))).symm
    _ = (t + 1) ^ (-(3 : ℝ)) := by
          exact congrArg (fun x : ℝ => x ^ (-(3 : ℝ))) (add_comm 1 t)

/-- Lebesgue measure on the real line is preserved by right translation. -/
theorem real_volume_preserving_addRight (a : ℝ) :
    MeasurePreserving (fun x : ℝ => x + a) volume volume := by
  exact
    { measurable := measurable_add_const a
      map_eq := map_add_right_eq_self volume a }

/-- Set-integral change of variables for translating a right ray by one. -/
theorem real_setIntegral_Ici_addRight_one
    (T : ℝ) (f : ℝ → ℝ) :
    (∫ t in Set.Ici T, f (t + 1))
      =
    (∫ u in Set.Ici (T + 1), f u) := by
  have hpres :
      MeasurePreserving (fun x : ℝ => x + 1) volume volume :=
    real_volume_preserving_addRight 1
  have hemb :
      MeasurableEmbedding (fun x : ℝ => x + 1) :=
    (Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding
  have himage :
      (fun x : ℝ => x + 1) '' Set.Ici T = Set.Ici (T + 1) :=
    image_add_const_Ici
  have hmap :
      (∫ u in (fun x : ℝ => x + 1) '' Set.Ici T, f u)
        =
      (∫ t in Set.Ici T, f (t + 1)) :=
    hpres.setIntegral_image_emb hemb f (Set.Ici T)
  exact
    Eq.trans hmap.symm
      (congrArg (fun s : Set ℝ => ∫ u in s, f u) himage)

/-- Removing the endpoint from the translated right ray does not change the
Lebesgue integral. -/
theorem real_setIntegral_Ici_shifted_eq_Ioi
    (T : ℝ) (f : ℝ → ℝ) :
    (∫ u in Set.Ici (T + 1), f u)
      =
    (∫ u in Set.Ioi (1 + T), f u) := by
  have hendpoint :
      (∫ u in Set.Ici (T + 1), f u)
        =
      (∫ u in Set.Ioi (T + 1), f u) :=
    integral_Ici_eq_integral_Ioi
  have hadd :
      T + 1 = 1 + T :=
    add_comm T 1
  exact
    Eq.trans hendpoint
      (congrArg (fun a : ℝ => ∫ u in Set.Ioi a, f u) hadd)

/-- On a nonnegative right tail, the inverse-cubic norm majorant is the
translated open-tail power integral. -/
theorem real_inverseCubic_rightTail_integral_eq_shifted_rpow_Ioi
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ) := by
  let shiftedWeight : ℝ → ℝ :=
    fun u : ℝ => u ^ (-(3 : ℝ))
  have hpoint :
      EqOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (fun t : ℝ => shiftedWeight (t + 1))
        (Set.Ici T) :=
    fun t ht =>
      real_inverseCubic_rightTail_value_eq_shifted_rpow T t hT ht
  have hclosed :
      (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
      (∫ t in Set.Ici T,
          shiftedWeight (t + 1)) :=
    setIntegral_congr_fun measurableSet_Ici hpoint
  have htranslated :
      (∫ t in Set.Ici T,
          shiftedWeight (t + 1))
        =
      (∫ u in Set.Ici (T + 1),
          shiftedWeight u) :=
    real_setIntegral_Ici_addRight_one T shiftedWeight
  have hopen :
      (∫ u in Set.Ici (T + 1),
          shiftedWeight u)
        =
      (∫ u in Set.Ioi (1 + T),
          shiftedWeight u) :=
    real_setIntegral_Ici_shifted_eq_Ioi T shiftedWeight
  exact Eq.trans hclosed (Eq.trans htranslated hopen)

/-- Numeric comparison needed for the inverse-cubic improper integral. -/
theorem negThree_lt_negOne_real :
    (-(3 : ℝ)) < -1 := by
  exact neg_lt_neg one_lt_three

/-- The exponent arithmetic in the `-3` tail antiderivative. -/
theorem negThree_add_one_eq_negTwo_real :
    (-(3 : ℝ) + 1) = -(2 : ℝ) := by
  have hThree :
      (3 : ℝ) = 2 + 1 :=
    Nat.cast_add 2 1
  calc
    (-(3 : ℝ) + 1)
        = -(2 + 1 : ℝ) + 1 := by
          exact congrArg (fun x : ℝ => -x + 1) hThree
    _ = (-(2 : ℝ) + -(1 : ℝ)) + 1 := by
          exact congrArg (fun x : ℝ => x + 1) (neg_add (2 : ℝ) 1)
    _ = -(2 : ℝ) + (-(1 : ℝ) + 1) := by
          exact add_assoc (-(2 : ℝ)) (-(1 : ℝ)) 1
    _ = -(2 : ℝ) + 0 := by
          exact congrArg (fun x : ℝ => -(2 : ℝ) + x) (neg_add_cancel (1 : ℝ))
    _ = -(2 : ℝ) := by
          exact add_zero (-(2 : ℝ))

/-- Division by two written in the orientation needed by the tail value. -/
theorem div_two_eq_half_mul_real (x : ℝ) :
    x / (2 : ℝ) = (1 / 2 : ℝ) * x := by
  have hOneDiv :
      (1 / 2 : ℝ) = (2 : ℝ)⁻¹ :=
    one_div (2 : ℝ)
  calc
    x / (2 : ℝ)
        = x * (2 : ℝ)⁻¹ := by
          exact div_eq_mul_inv x (2 : ℝ)
    _ = x * (1 / 2 : ℝ) := by
          exact congrArg (fun y : ℝ => x * y) hOneDiv.symm
    _ = (1 / 2 : ℝ) * x := by
          exact mul_comm x (1 / 2 : ℝ)

/-- The signed denominator in the `-3` tail antiderivative contributes the
factor `1 / 2`. -/
theorem neg_div_negTwo_eq_half_mul_real (x : ℝ) :
    -x / (-(2 : ℝ)) = (1 / 2 : ℝ) * x := by
  calc
    -x / (-(2 : ℝ))
        = x / (2 : ℝ) := by
          exact neg_div_neg_eq x (2 : ℝ)
    _ = (1 / 2 : ℝ) * x := by
          exact div_two_eq_half_mul_real x

/-- Transporting a real power across the `-3 + 1 = -2` exponent equality. -/
theorem rpow_negThree_add_one_eq_rpow_negTwo_real (c : ℝ) :
    c ^ (-(3 : ℝ) + 1) = c ^ (-(2 : ℝ)) := by
  exact congrArg (fun a : ℝ => c ^ a) negThree_add_one_eq_negTwo_real

/-- The antiderivative boundary value appearing in
`integral_Ioi_rpow_of_lt` for exponent `-3` is the expected half
inverse-square value. -/
theorem real_negThree_rpow_tail_antiderivative_value_eq_half_rpow_negTwo
    (c : ℝ) :
    -(c ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1)
      =
    (1 / 2 : ℝ) * c ^ (-(2 : ℝ)) := by
  calc
    -(c ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1)
        =
        -(c ^ (-(2 : ℝ))) / (-(2 : ℝ)) := by
          exact
            congrArg₂
              (fun x y : ℝ => -x / y)
              (rpow_negThree_add_one_eq_rpow_negTwo_real c)
              negThree_add_one_eq_negTwo_real
    _ = (1 / 2 : ℝ) * c ^ (-(2 : ℝ)) := by
          exact neg_div_negTwo_eq_half_mul_real (c ^ (-(2 : ℝ)))

/-- Specialization of the standard improper-integral computation to the
translated inverse-cubic power tail. -/
theorem real_shifted_rpow_Ioi_negThree_integral_eq_half_rpow_negTwo
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
      =
    (1 / 2 : ℝ) * (1 + T) ^ (-(2 : ℝ)) := by
  have hPositiveLower :
      0 < 1 + T :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hT)
  have hIntegral :
      (∫ u in Set.Ioi (1 + T),
          u ^ (-(3 : ℝ)) : ℝ)
        =
      -((1 + T) ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1) :=
    integral_Ioi_rpow_of_lt (a := -(3 : ℝ)) (c := 1 + T)
      negThree_lt_negOne_real
      hPositiveLower
  calc
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
        =
        -((1 + T) ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1) := by
          exact hIntegral
    _ =
        (1 / 2 : ℝ) * (1 + T) ^ (-(2 : ℝ)) := by
          exact real_negThree_rpow_tail_antiderivative_value_eq_half_rpow_negTwo
            (1 + T)

/-- On a nonnegative center, the shifted real-power boundary value is the same
as the integer-power norm boundary value used downstream. -/
theorem real_shifted_rpow_negTwo_eq_inverseQuadratic_boundary
    (T : ℝ) (hT : 0 ≤ T) :
    (1 + T) ^ (-(2 : ℝ))
      =
    (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (1 + T) ^ (-(2 : ℝ))
        =
        (1 + ‖T‖) ^ (-(2 : ℝ)) := by
          exact congrArg
            (fun x : ℝ => (1 + x) ^ (-(2 : ℝ)))
            (Real.norm_of_nonneg hT).symm
    _ =
        (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact Real.rpow_intCast (1 + ‖T‖) (-(2 : ℤ))

/-- The translated open inverse-cubic power tail has the sharp inverse-square
boundary value. -/
theorem real_shifted_rpow_Ioi_negThree_integral_eq_half_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
      =
    (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
        =
        (1 / 2 : ℝ) * (1 + T) ^ (-(2 : ℝ)) := by
          exact real_shifted_rpow_Ioi_negThree_integral_eq_half_rpow_negTwo
            T hT
    _ =
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact congrArg
            (fun x : ℝ => (1 / 2 : ℝ) * x)
            (real_shifted_rpow_negTwo_eq_inverseQuadratic_boundary T hT)

/-- The inverse-cubic norm majorant is invariant under real reflection. -/
theorem real_inverseCubic_reflection_value (t : ℝ) :
    (1 + ‖(-t)‖) ^ (-(3 : ℤ))
      =
    ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact congrArg (fun x : ℝ => (1 + x) ^ (-(3 : ℤ))) (norm_neg t)

/-- Reflecting the right closed tail across the origin gives the left closed
tail. -/
theorem preimage_neg_Ici_eq_Iic_neg (T : ℝ) :
    (fun t : ℝ => -t) ⁻¹' Set.Ici T = Set.Iic (-T) := by
  exact Set.ext (fun _ => le_neg)

/-- The reflected inverse-cubic set integral over the left tail is the
unreflected set integral over that same left tail. -/
theorem real_inverseCubic_leftTail_integral_eq_reflected_preimage
    (T : ℝ) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
        (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hSet :
      (fun t : ℝ => -t) ⁻¹' Set.Ici T = Set.Iic (-T) :=
    preimage_neg_Ici_eq_Iic_neg T
  have hPoint :
      ∀ t : ℝ,
        t ∈ Set.Iic (-T) →
          (1 + ‖t‖) ^ (-(3 : ℤ))
            =
          ((1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) :=
    fun t _ =>
      (real_inverseCubic_reflection_value t).symm
  calc
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in Set.Iic (-T),
          (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact setIntegral_congr_fun measurableSet_Iic hPoint
    _ =
        (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
          (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact congrArg
            (fun s : Set ℝ =>
              ∫ t in s, (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ)
            hSet.symm

/-- Set-integral change of variables for real reflection on the inverse-cubic
tail. -/
theorem real_inverseCubic_reflected_preimage_integral_eq_rightTail
    (T : ℝ) :
    (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
        (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact
    (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Ici T)

/-- The left closed inverse-cubic norm tail is the corresponding right closed
tail by the reflection symmetry of Lebesgue measure and the norm. -/
theorem real_inverseCubic_leftTail_integral_eq_rightTail
    (T : ℝ) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  calc
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
          (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_leftTail_integral_eq_reflected_preimage T
    _ =
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_reflected_preimage_integral_eq_rightTail T

/-- Sharp right half-line inverse-cubic tail evaluation up to the harmless
closed-endpoint convention. -/
theorem real_inverseCubic_rightTail_integral_half_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ u in Set.Ioi (1 + T),
          u ^ (-(3 : ℝ)) : ℝ) := by
          exact real_inverseCubic_rightTail_integral_eq_shifted_rpow_Ioi T hT
    _ =
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact real_shifted_rpow_Ioi_negThree_integral_eq_half_inverseQuadratic
            T hT
    _ ≤
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact le_rfl

/-- Sharp left half-line inverse-cubic tail evaluation up to the harmless
closed-endpoint convention. -/
theorem real_inverseCubic_leftTail_integral_half_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_leftTail_integral_eq_rightTail T
    _ ≤
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact real_inverseCubic_rightTail_integral_half_inverseQuadratic T hT

/-- The coefficient `1 / 2` is bounded by `2`. -/
theorem one_half_le_two_real :
    (1 / 2 : ℝ) ≤ 2 := by
  have hhalf_le_one :
      (1 / 2 : ℝ) ≤ 1 :=
    one_div_le_one zero_le_one one_le_two
  exact le_trans hhalf_le_one one_le_two

/-- The inverse-quadratic boundary term is nonnegative. -/
theorem real_inverseQuadratic_boundary_nonnegative
    (T : ℝ) :
    0 ≤ ((1 + ‖T‖) ^ (-(2 : ℤ)) : ℝ) := by
  exact zpow_nonneg (add_nonneg zero_le_one (norm_nonneg T)) (-(2 : ℤ))

/-- The sharp half-coefficient inverse-quadratic bound implies the looser
coefficient used downstream. -/
theorem real_inverseCubic_halfBound_le_twoBound
    (T : ℝ) :
    (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ))
      ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  exact mul_le_mul_of_nonneg_right
    one_half_le_two_real
    (real_inverseQuadratic_boundary_nonnegative T)

/-- Right half-line inverse-cubic tail bound. -/
theorem real_inverseCubic_rightTail_integral_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  exact le_trans
    (real_inverseCubic_rightTail_integral_half_inverseQuadratic T hT)
    (real_inverseCubic_halfBound_le_twoBound T)

/-- Left half-line inverse-cubic tail bound. -/
theorem real_inverseCubic_leftTail_integral_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  exact le_trans
    (real_inverseCubic_leftTail_integral_half_inverseQuadratic T hT)
    (real_inverseCubic_halfBound_le_twoBound T)

/-- The complement of a symmetric interval is contained in the union of the two
outer half-lines. -/
theorem compl_symmetricIcc_subset_leftTail_union_rightTail
    (T : ℝ) :
    (Set.Icc (-T) T)ᶜ ⊆ Set.Iic (-T) ∪ Set.Ici T := by
  intro x hx
  by_cases hleft : x ≤ -T
  · exact Or.inl hleft
  · have hneg_left : -T < x := lt_of_not_ge hleft
    have hT_le_x : T ≤ x := by
      by_contra hxT
      exact hx ⟨le_of_lt hneg_left, le_of_not_ge hxT⟩
    exact Or.inr hT_le_x

/-- Pointwise nonnegativity of the scalar inverse-cubic majorant. -/
theorem real_inverseCubic_pointwise_nonnegative
    (t : ℝ) :
    0 ≤ ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact zpow_nonneg (add_nonneg zero_le_one (norm_nonneg t)) (-(3 : ℤ))

/-- The scalar inverse-cubic majorant is nonnegative almost everywhere on any
tail union. -/
theorem real_inverseCubic_tailUnion_ae_nonnegative
    (T : ℝ) :
    0 ≤ᵐ[volume.restrict (Set.Iic (-T) ∪ Set.Ici T)]
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact Eventually.of_forall
    (fun t : ℝ => real_inverseCubic_pointwise_nonnegative t)

/-- The scalar inverse-cubic majorant is globally integrable. -/
theorem real_inverseCubic_integrable :
    Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hDimension :
      ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 := by
    exact congrArg
      (fun n : ℕ => (n : ℝ))
      (Module.finrank_self ℝ)
  have hDimensionBound :
      ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 3 := by
    calc
      ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 := by
        exact hDimension
      _ < 3 := by
        exact one_lt_three
  have hRpow :
      Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)) : ℝ) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) hDimensionBound
  exact hRpow.congr
    (Eventually.of_forall
      (fun t : ℝ =>
        Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))))

/-- Integrability of the scalar inverse-cubic majorant on a closed right
half-line tail. -/
theorem real_inverseCubic_integrableOn_rightTail
    (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Ici T) := by
  exact real_inverseCubic_integrable.integrableOn

/-- Integrability of the scalar inverse-cubic majorant on a closed left
half-line tail. -/
theorem real_inverseCubic_integrableOn_leftTail
    (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Iic (-T)) := by
  exact real_inverseCubic_integrable.integrableOn

/-- Integrability of the scalar inverse-cubic majorant on the union of the two
outer closed half-line tails. -/
theorem real_inverseCubic_integrableOn_leftTail_union_rightTail
    (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Iic (-T) ∪ Set.Ici T) := by
  exact
    (real_inverseCubic_integrableOn_leftTail T).union
      (real_inverseCubic_integrableOn_rightTail T)

/-- For a nonnegative radius, the intersection of the two closed outer tails is
subsingleton. -/
theorem leftTail_rightTail_inter_subsingleton_of_nonnegative
    (T : ℝ) (hT : 0 ≤ T) :
    (Set.Iic (-T) ∩ Set.Ici T).Subsingleton := by
  have hNegT_le_T : -T ≤ T :=
    le_trans (neg_nonpos.mpr hT) hT
  exact (Set.subsingleton_Icc_of_ge hNegT_le_T).mono
    (fun x hx => ⟨hx.right, hx.left⟩)

/-- The two closed tails are a.e.-disjoint with respect to Lebesgue measure
when the center radius is nonnegative. -/
theorem leftTail_rightTail_aedisjoint_of_nonnegative
    (T : ℝ) (hT : 0 ≤ T) :
    AEDisjoint volume (Set.Iic (-T)) (Set.Ici T) := by
  exact
    (leftTail_rightTail_inter_subsingleton_of_nonnegative T hT).measure_zero
      volume

/-- The scalar inverse-cubic integral over the two-tail union is bounded by the
sum of the two closed-tail integrals. -/
theorem real_inverseCubic_tailUnionIntegral_le_left_plus_right
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Iic (-T) ∪ Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hIntegrableUnion :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Iic (-T) ∪ Set.Ici T) :=
    real_inverseCubic_integrableOn_leftTail_union_rightTail T
  have hIntegrableLeft :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Iic (-T)) :=
    hIntegrableUnion.left_of_union
  have hIntegrableRight :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Ici T) :=
    hIntegrableUnion.right_of_union
  calc
    (∫ t in Set.Iic (-T) ∪ Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact integral_union_ae
            (leftTail_rightTail_aedisjoint_of_nonnegative T hT)
            measurableSet_Ici.nullMeasurableSet
            hIntegrableLeft
            hIntegrableRight
    _ ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact le_rfl

/-- The symmetric complement inverse-cubic integral is bounded by the sum of
the two half-line tail integrals. -/
theorem real_inverseCubic_symmetricComplementIntegral_le_left_plus_right
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hUnionIntegrable :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Iic (-T) ∪ Set.Ici T) :=
    real_inverseCubic_integrableOn_leftTail_union_rightTail T
  have hNonnegative :
      0 ≤ᵐ[volume.restrict (Set.Iic (-T) ∪ Set.Ici T)]
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) :=
    real_inverseCubic_tailUnion_ae_nonnegative T
  have hSubset :
      (Set.Icc (-T) T)ᶜ ≤ᵐ[volume] Set.Iic (-T) ∪ Set.Ici T :=
    (compl_symmetricIcc_subset_leftTail_union_rightTail T).eventuallyLE
  calc
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤
        (∫ t in Set.Iic (-T) ∪ Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact setIntegral_mono_set hUnionIntegrable hNonnegative hSubset
    _ ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_tailUnionIntegral_le_left_plus_right T hT

/-- Fixed-height inverse-cubic tails outside a symmetric interval have
inverse-quadratic size. -/
theorem real_inverseCubic_symmetricComplementIntegral_inverseQuadratic_of_nonnegative
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ 4 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  have hleft :
      (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
    real_inverseCubic_leftTail_integral_inverseQuadratic T hT
  have hright :
      (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
    real_inverseCubic_rightTail_integral_inverseQuadratic T hT
  calc
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤
          (∫ t in Set.Iic (-T),
            (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
          (∫ t in Set.Ici T,
            (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_symmetricComplementIntegral_le_left_plus_right T hT
    _ ≤
        2 * (1 + ‖T‖) ^ (-(2 : ℤ)) +
          2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact add_le_add hleft hright
    _ = 4 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          calc
            2 * (1 + ‖T‖) ^ (-(2 : ℤ)) +
                2 * (1 + ‖T‖) ^ (-(2 : ℤ))
                =
                (2 + 2) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
                  exact (add_mul 2 2 ((1 + ‖T‖) ^ (-(2 : ℤ)))).symm
            _ = 4 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
                  exact rfl

/-- The real inverse-cubic majorant has inverse-quadratic tails outside
symmetric intervals. -/
theorem real_inverseCubic_symmetricComplementIntegral_inverseQuadratic
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ᶠ u in atTop,
          (∫ t in (Set.Icc (-(height u)) (height u))ᶜ,
              (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
            ≤ A * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  refine ⟨4, by exact zero_lt_four, ?_⟩
  exact (cofinalHeight_eventually_nonnegative height hcofinal).mono
    (fun u hu =>
      real_inverseCubic_symmetricComplementIntegral_inverseQuadratic_of_nonnegative
        (height u) hu)

/-- Norm domination by an inverse-cubic majorant controls the symmetric
Bochner tail by the corresponding scalar majorant tail. -/
theorem fixedRightLine_integrableFunction_symmetricTail_norm_le_majorantTail
    (G : ℝ → ℂ) (hG_aesm : AEStronglyMeasurable G volume)
    (C : ℝ) (hC : 0 < C)
    (height : ℝ → ℝ)
    (hG :
      ∀ t : ℝ,
        ‖G t‖ ≤ C * (1 + ‖t‖) ^ (-(3 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
          (∫ t : ℝ, G t)‖
        ≤ C *
          (∫ t in (Set.Icc (-(height u)) (height u))ᶜ,
            (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hMajorantIntegrable :
      Integrable
        (fun t : ℝ => C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ))
        volume :=
    real_inverseCubic_integrable.const_mul C
  have hG_integrable : Integrable G volume :=
    hMajorantIntegrable.mono' hG_aesm
      (Eventually.of_forall hG)
  exact Filter.Eventually.of_forall
    (fun u : ℝ =>
      let s : Set ℝ := Set.Icc (-(height u)) (height u)
      have hs : MeasurableSet s :=
        measurableSet_Icc
      have hcompl :
          ∫ t in sᶜ, G t = ∫ t : ℝ, G t - ∫ t in s, G t :=
        setIntegral_compl hs hG_integrable
      have hdiff :
          (∫ t in s, G t) - (∫ t : ℝ, G t)
            =
          -(∫ t in sᶜ, G t) := by
        calc
          (∫ t in s, G t) - (∫ t : ℝ, G t)
              =
            -((∫ t : ℝ, G t) - (∫ t in s, G t)) := by
              exact (neg_sub (∫ t : ℝ, G t) (∫ t in s, G t)).symm
          _ = -(∫ t in sᶜ, G t) := by
              exact congrArg Neg.neg hcompl.symm
      have hnormComplement :
          ‖(∫ t in s, G t) - (∫ t : ℝ, G t)‖
            =
          ‖∫ t in sᶜ, G t‖ := by
        calc
          ‖(∫ t in s, G t) - (∫ t : ℝ, G t)‖
              = ‖-(∫ t in sᶜ, G t)‖ := by
                exact congrArg norm hdiff
          _ = ‖∫ t in sᶜ, G t‖ := by
                exact norm_neg (∫ t in sᶜ, G t)
      have hNormIntegral :
          ‖∫ t in sᶜ, G t‖
            ≤
          ∫ t in sᶜ, ‖G t‖ :=
        norm_integral_le_integral_norm
          (μ := volume.restrict sᶜ) G
      have hMajorantOn :
          ∫ t in sᶜ, ‖G t‖
            ≤
          ∫ t in sᶜ,
            C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) :=
        setIntegral_mono_on
          hG_integrable.norm.integrableOn
          hMajorantIntegrable.integrableOn
          hs.compl
          (fun t _ht => hG t)
      have hConstOut :
          (∫ t in sᶜ,
            C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ))
            =
          C *
            (∫ t in sᶜ,
              ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)) :=
        integral_mul_left (μ := volume.restrict sᶜ) C
          (fun t : ℝ => ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ))
      calc
        ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
            (∫ t : ℝ, G t)‖
            = ‖(∫ t in s, G t) - (∫ t : ℝ, G t)‖ := by
              exact rfl
        _ = ‖∫ t in sᶜ, G t‖ := by
              exact hnormComplement
        _ ≤ ∫ t in sᶜ, ‖G t‖ := by
              exact hNormIntegral
        _ ≤
            ∫ t in sᶜ,
              C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
              exact hMajorantOn
        _ = C *
            (∫ t in sᶜ,
              ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)) := by
              exact hConstOut)

/-- Inverse-cubic pointwise decay gives an inverse-quadratic symmetric
truncation tail along any cofinal height schedule. -/
theorem fixedRightLine_integrableFunction_symmetricTail_inverseQuadratic_of_inverseCubicDecay
    (G : ℝ → ℂ) (hG_aesm : AEStronglyMeasurable G volume)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop)
    (C : ℝ) (hC : 0 < C)
    (hG :
      ∀ t : ℝ,
        ‖G t‖ ≤ C * (1 + ‖t‖) ^ (-(3 : ℤ))) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
              (∫ t : ℝ, G t)‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match real_inverseCubic_symmetricComplementIntegral_inverseQuadratic height hcofinal with
  | ⟨A, hA_pos, hA_eventual⟩ =>
      refine ⟨C * A, mul_pos hC hA_pos, ?_⟩
      exact
        ((fixedRightLine_integrableFunction_symmetricTail_norm_le_majorantTail
          G hG_aesm C hC height hG).and hA_eventual).mono
          (fun u hu =>
            calc
              ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
                  (∫ t : ℝ, G t)‖
                  ≤ C *
                    (∫ t in (Set.Icc (-(height u)) (height u))ᶜ,
                      (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := hu.1
              _ ≤ C * (A * (1 + ‖height u‖) ^ (-(2 : ℤ))) := by
                    exact mul_le_mul_of_nonneg_left hu.2 (le_of_lt hC)
              _ = C * A * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
                    exact (mul_assoc C A
                      ((1 + ‖height u‖) ^ (-(2 : ℤ)))).symm)

/-- Inverse-quadratic symmetric tail control identifies the full-line integral
as the limit of symmetric truncations. -/
theorem fixedRightLine_integrableFunction_symmetricTruncation_tendsto_fullLine_of_inverseQuadraticTail
    (G : ℝ → ℂ) (height : ℝ → ℝ)
    (hcofinal : Tendsto height atTop atTop)
    (htail :
      ∃ MR : ℝ,
        0 < MR ∧
          ∀ᶠ u in atTop,
            ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
                (∫ t : ℝ, G t)‖
              ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc (-(height u)) (height u), G t)
      atTop
      (𝓝 (∫ t : ℝ, G t)) := by
  match htail with
  | ⟨MR, hMR_pos, hMR_eventual⟩ =>
      have hMR_nonneg : 0 ≤ MR :=
        le_of_lt hMR_pos
      have hdecay :
          Tendsto
            (fun u : ℝ =>
              MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
            atTop
            (𝓝 (MR * 0)) :=
        tendsto_const_nhds.mul
          (cofinalHeight_one_add_norm_inverseQuadratic_tendsto_zero
            height hcofinal)
      have hzero :
          MR * (0 : ℝ) = 0 :=
        mul_zero MR
      have hmajorant :
          Tendsto
            (fun u : ℝ =>
              MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
            atTop
            (𝓝 0) :=
        hzero ▸ hdecay
      exact
        tendsto_iff_norm_sub_tendsto_zero.2
          (squeeze_zero_norm' hMR_eventual hmajorant)

/-- The fixed right-line Fourier-Cauchy multiplier integrand is strongly
measurable in the frequency variable. -/
theorem fixedRightLine_fourierCauchy_multiplierIntegrand_aestronglyMeasurable
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      volume := by
  have hK_pair :
      Continuous (fun p : ℝ × ℝ => K p.2) :=
    hK_cont.comp continuous_snd
  have hphase :
      Continuous
        (fun p : ℝ × ℝ =>
          Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) :=
    (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp continuous_snd)
  have hweight :
      Continuous
        (fun p : ℝ × ℝ =>
          (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)
  have hjoint :
      Continuous
        (fun p : ℝ × ℝ =>
          K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) :=
    (hK_pair.mul (Complex.continuous_exp.comp hphase)).mul
      (Complex.continuous_exp.comp hweight)
  have hinner :
      AEStronglyMeasurable
        (fun t : ℝ =>
          ∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        volume :=
    (hjoint.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hden :
      Measurable
        (fun t : ℝ => (((c : ℂ) + t * Complex.I) - 1)) :=
    ((measurable_const.add
      ((Complex.continuous_ofReal.measurable).mul measurable_const)).sub
      measurable_const)
  have hmultiplier :
      AEStronglyMeasurable
        (fun t : ℝ => -1 / (((c : ℂ) + t * Complex.I) - 1))
        volume :=
    ((measurable_const.div hden).aestronglyMeasurable)
  exact hmultiplier.mul hinner

/-- Generic inverse-quadratic truncation tail for the fixed right
Fourier-Cauchy multiplier. -/
theorem fixedRightLine_fourierCauchy_truncationTail_inverseQuadratic
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                (∫ x : ℝ,
                  K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) -
            (∫ t : ℝ,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                (∫ x : ℝ,
                  K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match
    fixedRightLine_fourierCauchy_multiplierIntegrand_inverseCubicDecay
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        fixedRightLine_integrableFunction_symmetricTail_inverseQuadratic_of_inverseCubicDecay
          (fun t : ℝ =>
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
          (fixedRightLine_fourierCauchy_multiplierIntegrand_aestronglyMeasurable
            K hK_cont hK_compact hK_smooth c hc)
          height hcofinal C hC_pos hC_bound

/-- Symmetric truncations of the smooth fixed-line Fourier-Cauchy multiplier
converge to the full-line ordinary integral. -/
theorem fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_fullLine
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ t : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))) := by
  exact
    fixedRightLine_integrableFunction_symmetricTruncation_tendsto_fullLine_of_inverseQuadraticTail
      (fun t : ℝ =>
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      (fun T : ℝ => T)
      tendsto_id
      (fixedRightLine_fourierCauchy_truncationTail_inverseQuadratic
        K hK_cont hK_compact hK_smooth c hc
        (fun T : ℝ => T)
        tendsto_id)

/-- The scalar Cauchy kernel indicator integral is the one-sided projection
integral. -/
theorem fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
    (K : ℝ → ℂ) :
    (∫ x : ℝ,
        K x *
          Set.indicator (Set.Ici (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  calc
    (∫ x : ℝ,
        K x *
          Set.indicator (Set.Ici (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)
        =
        ∫ x : ℝ,
          Set.indicator (Set.Ici (0 : ℝ))
            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
          exact integral_congr_ae
            (Eventually.of_forall
              (fun x : ℝ =>
                if hx : x ∈ Set.Ici (0 : ℝ) then
                  calc
                    K x *
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x
                        = K x * (-2 * (Real.pi : ℂ)) := by
                          exact congrArg
                            (fun z : ℂ => K x * z)
                            (indicator_of_mem hx
                              (fun _ : ℝ => (-2 * (Real.pi : ℂ))))
                    _ = (-2 * (Real.pi : ℂ)) * K x := by
                          exact mul_comm (K x) (-2 * (Real.pi : ℂ))
                    _ =
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
                          exact (indicator_of_mem hx
                            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)).symm
                else
                  calc
                    K x *
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x
                        = K x * 0 := by
                          exact congrArg
                            (fun z : ℂ => K x * z)
                            (indicator_of_not_mem hx
                              (fun _ : ℝ => (-2 * (Real.pi : ℂ))))
                    _ = 0 := by
                          exact mul_zero (K x)
                    _ =
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
                          exact (indicator_of_not_mem hx
                            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)).symm))
    _ =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x := by
          exact integral_indicator measurableSet_Ici

/-- Product integrability for the finite-window fixed-right-line Cauchy kernel. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_productIntegrable
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
      (Set.Icc (-T) T ×ˢ Set.univ) := by
  let F : ℝ × ℝ → ℂ :=
    fun p : ℝ × ℝ =>
      (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
        K p.2 *
        Complex.exp
          (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))
  have hden :
      Continuous
        (fun p : ℝ × ℝ =>
          (((c : ℂ) + p.1 * Complex.I) - 1)) :=
    (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).sub
      continuous_const
  have hden_ne :
      ∀ p : ℝ × ℝ,
        (((c : ℂ) + p.1 * Complex.I) - 1) ≠ 0 :=
    fun p : ℝ × ℝ =>
      fixedRightLine_cauchyDenominator_ne_zero c p.1 hc
  have hscalar :
      Continuous
        (fun p : ℝ × ℝ =>
          -1 / (((c : ℂ) + p.1 * Complex.I) - 1)) :=
    continuous_const.div hden hden_ne
  have hK_pair :
      Continuous (fun p : ℝ × ℝ => K p.2) :=
    hK_cont.comp continuous_snd
  have hphase :
      Continuous
        (fun p : ℝ × ℝ =>
          Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) :=
    (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp continuous_snd)
  have hweight :
      Continuous
        (fun p : ℝ × ℝ =>
          ((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)
  have hF_cont : Continuous F :=
    ((hscalar.mul hK_pair).mul
      (Complex.continuous_exp.comp hphase)).mul
        (Complex.continuous_exp.comp hweight)
  have hcompact :
      IsCompact (Set.Icc (-T) T ×ˢ tsupport K) :=
    isCompact_Icc.prod hK_compact
  have hF_compact :
      IntegrableOn F (Set.Icc (-T) T ×ˢ tsupport K) :=
    hF_cont.continuousOn.integrableOn_compact hcompact
  exact
    hF_compact.of_forall_diff_eq_zero
      (measurableSet_Icc.prod measurableSet_univ)
      (fun p hp =>
        let hnot :
            p.2 ∉ tsupport K :=
          fun hp_support =>
            hp.2 ⟨hp.1.1, hp_support⟩
        calc
          F p =
              (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
                K p.2 *
                Complex.exp
                  (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact rfl
          _ =
              (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
                0 *
                Complex.exp
                  (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact congrArg
                  (fun z : ℂ =>
                    (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
                      z *
                      Complex.exp
                        (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
                  (image_eq_zero_of_nmem_tsupport hnot)
          _ =
              0 *
                Complex.exp
                  (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact congrArg
                  (fun z : ℂ =>
                    z *
                      Complex.exp
                        (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
                  (mul_zero
                    (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)))
          _ =
              0 *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact congrArg
                  (fun z : ℂ =>
                    z *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
                  (zero_mul
                    (Complex.exp
                      (Complex.I * (p.1 : ℂ) * (p.2 : ℂ))))
          _ = 0 := by
                exact zero_mul
                  (Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))

/-- Standard Fubini form of the finite-window product Cauchy integral. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_productIntegral_eq_iterated
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) =
      ∫ t in Set.Icc (-T) T,
        ∫ x : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  exact
    setIntegral_prod
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
      (fixedRightLine_fourierCauchy_symmetricWindow_productIntegrable
        K hK_cont hK_compact hK_smooth c hc T)

/-- Pointwise reassociation for pulling the fixed Cauchy scalar outside the
inner time-side integral. -/
theorem fixedRightLine_outerScalar_integrand_reassoc
    (K : ℝ → ℂ) (c t x : ℝ) :
    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        (K x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        K x *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  calc
    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        (K x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact mul_assoc
            (-1 / (((c : ℂ) + t * Complex.I) - 1))
            (K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
    _ =
        (((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ =>
              z *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
            (mul_assoc
              (-1 / (((c : ℂ) + t * Complex.I) - 1))
              (K x)
              (Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))))
    _ =
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact (mul_assoc
            ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x)
            (Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))).symm

/-- The finite-window iterated product integral pulls the Cauchy scalar outside
the inner time-side integral. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_iterated_eq_outerScalarIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
        ∫ x : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      ∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
  exact
    integral_congr_ae
      (Eventually.of_forall
        (fun t : ℝ =>
          calc
            (∫ x : ℝ,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
                =
                ∫ x : ℝ,
                  (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                    (K x *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                  exact
                    integral_congr_ae
                      (Eventually.of_forall
                        (fun x : ℝ =>
                          (fixedRightLine_outerScalar_integrand_reassoc
                            K c t x).symm))
            _ =
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  (∫ x : ℝ,
                    K x *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                  exact
                    integral_mul_left
                      (-1 / (((c : ℂ) + t * Complex.I) - 1))
                      (fun x : ℝ =>
                        K x *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))))

/-- The finite-window fixed-right-line Cauchy integral is the corresponding
product integral. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ t in Set.Icc (-T) T,
          ∫ x : ℝ,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact
            (fixedRightLine_fourierCauchy_symmetricWindow_iterated_eq_outerScalarIntegral
              K hK_cont hK_compact hK_smooth c hc T).symm
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            (fixedRightLine_fourierCauchy_symmetricWindow_productIntegral_eq_iterated
              K hK_cont hK_compact hK_smooth c hc T).symm

/-- Pointwise commutative reassociation for the scalar-window integrand. -/
theorem fixedRightLine_scalarWindow_constMul_integrand_reassoc
    (K : ℝ → ℂ) (c t x : ℝ) :
    K x *
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        K x *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  calc
    K x *
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        (K x *
          ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact mul_assoc (K x)
            ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
    _ =
        ((K x * (-1 / (((c : ℂ) + t * Complex.I) - 1))) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ =>
              z *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
            (mul_assoc (K x)
              (-1 / (((c : ℂ) + t * Complex.I) - 1))
              (Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))))
    _ =
        (((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ =>
              (z *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ))) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
            (mul_comm (K x)
              (-1 / (((c : ℂ) + t * Complex.I) - 1)))
    _ =
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact (mul_assoc
            ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x)
            (Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))).symm

/-- The scalar-window expression is the reversed iterated product integral. -/
theorem fixedRightLine_scalarWindowIntegral_eq_reversedIterated
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  exact
    integral_congr_ae
      (Eventually.of_forall
        (fun x : ℝ =>
          calc
            K x *
                (∫ t in Set.Icc (-T) T,
                  (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
                =
                ∫ t in Set.Icc (-T) T,
                  K x *
                    ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                  exact
                    (integral_mul_left
                      (K x)
                      (fun t : ℝ =>
                        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))).symm
            _ =
                ∫ t in Set.Icc (-T) T,
                  (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                    K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
                  exact
                    integral_congr_ae
                      (Eventually.of_forall
                        (fun t : ℝ =>
                          fixedRightLine_scalarWindow_constMul_integrand_reassoc
                            K c t x))))

/-- Swapped-coordinate product integrability for the finite-window scalar
Cauchy kernel. -/
theorem fixedRightLine_scalarWindow_swappedProductIntegrable
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    IntegrableOn
      (fun q : ℝ × ℝ =>
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
      (Set.univ ×ˢ Set.Icc (-T) T) := by
  let F : ℝ × ℝ → ℂ :=
    fun p : ℝ × ℝ =>
      (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
        K p.2 *
        Complex.exp
          (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))
  let G : ℝ × ℝ → ℂ :=
    fun q : ℝ × ℝ =>
      (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
        K q.1 *
        Complex.exp
          (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))
  have hF_set :
      IntegrableOn F (Set.Icc (-T) T ×ˢ Set.univ) :=
    fixedRightLine_fourierCauchy_symmetricWindow_productIntegrable
      K hK_cont hK_compact hK_smooth c hc T
  have hF_product :
      Integrable F
        ((volume.restrict (Set.Icc (-T) T)).prod
          (volume.restrict Set.univ)) :=
    Eq.mp
      (congrArg
        (fun μ : MeasureTheory.Measure (ℝ × ℝ) => Integrable F μ)
        (MeasureTheory.Measure.prod_restrict
          (μ := volume) (ν := volume)
          (s := Set.Icc (-T) T) (t := Set.univ)).symm)
      hF_set
  have hG_product :
      Integrable G
        ((volume.restrict Set.univ).prod
          (volume.restrict (Set.Icc (-T) T))) :=
    hF_product.swap
  exact
    Eq.mp
      (congrArg
        (fun μ : MeasureTheory.Measure (ℝ × ℝ) => Integrable G μ)
        (MeasureTheory.Measure.prod_restrict
          (μ := volume) (ν := volume)
          (s := Set.univ) (t := Set.Icc (-T) T)))
      hG_product

/-- Reversed Fubini form of the scalar-window product integral. -/
theorem fixedRightLine_scalarWindow_reversedIterated_eq_swappedProductIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      ∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)) := by
  exact
    (setIntegral_prod
      (fun q : ℝ × ℝ =>
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
      (fixedRightLine_scalarWindow_swappedProductIntegrable
        K hK_cont hK_compact hK_smooth c hc T)).symm

/-- Swapping coordinates sends the reversed product integral to the standard
finite-window product integral. -/
theorem fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral_measureSwap
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ q,
        ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
        ∂((volume.restrict Set.univ).prod
          (volume.restrict (Set.Icc (-T) T)))) =
      ∫ p,
        ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
        ∂((volume.restrict (Set.Icc (-T) T)).prod
          (volume.restrict Set.univ)) := by
  exact
    integral_prod_swap
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))

/-- Set-integral normalization for the swapped finite-window product integral. -/
theorem fixedRightLine_scalarWindow_swappedProduct_setIntegral_eq_restrictedProductIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))) =
      ∫ q,
        ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
        ∂((volume.restrict Set.univ).prod
          (volume.restrict (Set.Icc (-T) T))) := by
  exact
    (congrArg
      (fun μ : MeasureTheory.Measure (ℝ × ℝ) =>
        ∫ q,
          ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
            K q.1 *
            Complex.exp
              (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))) ∂μ)
      (MeasureTheory.Measure.prod_restrict
        (μ := volume) (ν := volume)
        (s := Set.univ) (t := Set.Icc (-T) T))).symm

/-- Set-integral normalization for the standard finite-window product integral. -/
theorem fixedRightLine_scalarWindow_product_setIntegral_eq_restrictedProductIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) =
      ∫ p,
        ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
        ∂((volume.restrict (Set.Icc (-T) T)).prod
          (volume.restrict Set.univ)) := by
  exact
    (congrArg
      (fun μ : MeasureTheory.Measure (ℝ × ℝ) =>
        ∫ p,
          ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) ∂μ)
      (MeasureTheory.Measure.prod_restrict
        (μ := volume) (ν := volume)
        (s := Set.Icc (-T) T) (t := Set.univ))).symm

/-- Swapping coordinates sends the reversed product integral to the standard
finite-window product integral. -/
theorem fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
        =
        ∫ q,
          ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
            K q.1 *
            Complex.exp
              (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
          ∂((volume.restrict Set.univ).prod
            (volume.restrict (Set.Icc (-T) T))) := by
          exact
            fixedRightLine_scalarWindow_swappedProduct_setIntegral_eq_restrictedProductIntegral
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p,
          ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
          ∂((volume.restrict (Set.Icc (-T) T)).prod
            (volume.restrict Set.univ)) := by
          exact
            fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral_measureSwap
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            (fixedRightLine_scalarWindow_product_setIntegral_eq_restrictedProductIntegral
              K hK_cont hK_compact hK_smooth c hc T).symm

/-- Reversed Fubini form of the scalar-window product integral. -/
theorem fixedRightLine_scalarWindow_reversedIterated_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        ∫ q in Set.univ ×ˢ Set.Icc (-T) T,
          (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
            K q.1 *
            Complex.exp
              (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)) := by
          exact
            fixedRightLine_scalarWindow_reversedIterated_eq_swappedProductIntegral
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T

/-- The scalar-window integral is the same finite-window product integral. -/
theorem fixedRightLine_scalarWindowIntegral_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        ∫ x : ℝ,
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact
            fixedRightLine_scalarWindowIntegral_eq_reversedIterated
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            fixedRightLine_scalarWindow_reversedIterated_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T

/-- Finite-window Fubini form of the fixed-right-line Cauchy kernel. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_eq_scalarWindowIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
  calc
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            fixedRightLine_fourierCauchy_symmetricWindow_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact
            (fixedRightLine_scalarWindowIntegral_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T).symm

/-- The one-sided scalar projection is unchanged if the endpoint is removed,
because the endpoint has zero Lebesgue mass. -/
theorem fixedRightLine_scalarProjection_Ioi_integral_eq_Ici_integral
    (K : ℝ → ℂ) :
    (∫ x in Set.Ioi (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  exact (integral_Ici_eq_integral_Ioi : _).symm

/-- Positive-time residue value for the normalized Fourier-Laplace denominator.

This is the scalar contour-residue calculation before truncation limits are
transported back to symmetric real-line windows. -/

end FixedLineCauchyProjection

end
end Boundary
