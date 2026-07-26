import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleFiniteInterpolation.ZetaAdmissibleBump.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Compactly supported Gaussian admissible probes

Multiply the standard real Gaussian by the canonical admissible bump.  The
result is a concrete compactly supported smooth probe, equal to the Gaussian
on the inner ball and zero outside the outer ball.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ContDiff

theorem naturalOrder_le_contDiffInfinity (order : ℕ) :
    (order : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop
    (le_refl (∞ : WithTop ℕ∞))
    order

/-- The fixed compact bump profile from which every Gaussian cutoff is
obtained by inverse-radius scaling. -/
noncomputable def admissibleGaussianUnitBumpProfile (t : ℝ) : ℂ :=
  admissibleBump 0 1 2 zero_lt_one one_lt_two t

/-- The fixed Gaussian bump profile is smooth. -/
theorem admissibleGaussianUnitBumpProfile_contDiff :
    ContDiff ℝ ∞ admissibleGaussianUnitBumpProfile := by
  exact (admissibleBump 0 1 2 zero_lt_one one_lt_two).smooth

/-- Division by a nonzero radius is inverse scalar multiplication on the
real line. -/
theorem real_div_eq_inverse_smul
    (radius t : ℝ) :
    t / radius = radius⁻¹ • t := by
  exact Eq.trans
    (div_eq_inv_mul t radius)
    (Algebra.id.smul_eq_mul (R := ℝ) (radius⁻¹) t).symm

/-- Arbitrary iterated derivatives of the scaled fixed bump profile expose
one inverse-radius factor for every derivative. -/
theorem iteratedDeriv_admissibleGaussianUnitBumpProfile_div
    (radius : ℝ)
    (order : ℕ)
    (t : ℝ) :
    iteratedDeriv order
        (fun u : ℝ => admissibleGaussianUnitBumpProfile (u / radius))
        t =
      radius⁻¹ ^ order •
        iteratedDeriv order admissibleGaussianUnitBumpProfile
          (t / radius) := by
  have hfiniteSmooth :
      ContDiff ℝ order admissibleGaussianUnitBumpProfile :=
    admissibleGaussianUnitBumpProfile_contDiff.of_le
      (naturalOrder_le_contDiffInfinity order)
  have hfunction :
      (fun u : ℝ => admissibleGaussianUnitBumpProfile (u / radius)) =
        (fun u : ℝ =>
          admissibleGaussianUnitBumpProfile (radius⁻¹ * u)) := by
    funext u
    exact congrArg admissibleGaussianUnitBumpProfile
      (Eq.trans
        (real_div_eq_inverse_smul radius u)
        (Algebra.id.smul_eq_mul (R := ℝ) (radius⁻¹) u))
  have hscaled :=
    congrFun
      (iteratedDeriv_const_smul
        hfiniteSmooth
        radius⁻¹)
      t
  exact Eq.subst
    (motive := fun function : ℝ → ℂ =>
      iteratedDeriv order function t =
        radius⁻¹ ^ order •
          iteratedDeriv order admissibleGaussianUnitBumpProfile
            (t / radius))
    hfunction.symm
    (Eq.subst
      (motive := fun point : ℝ =>
        iteratedDeriv order
            (fun u : ℝ =>
              admissibleGaussianUnitBumpProfile (radius⁻¹ * u))
            t =
          radius⁻¹ ^ order •
            iteratedDeriv order admissibleGaussianUnitBumpProfile point)
      (Eq.trans
        (Algebra.id.smul_eq_mul (R := ℝ) (radius⁻¹) t).symm
        (real_div_eq_inverse_smul radius t).symm)
      hscaled)

/-- Every iterated derivative of the fixed bump profile has compact support. -/
theorem admissibleGaussianUnitBumpProfile_iteratedDeriv_hasCompactSupport
    (order : ℕ) :
    HasCompactSupport
      (iteratedDeriv order admissibleGaussianUnitBumpProfile) := by
  induction order with
  | zero =>
      have hprofile :
          HasCompactSupport admissibleGaussianUnitBumpProfile :=
        (admissibleBump 0 1 2 zero_lt_one one_lt_two).toZetaTestFunction.hasCompactSupport
      exact Eq.mpr
        (congrArg HasCompactSupport
          (iteratedDeriv_zero
            (f := admissibleGaussianUnitBumpProfile)).symm)
        hprofile
  | succ order hprevious =>
      have hderivative :
          HasCompactSupport
            (deriv
              (iteratedDeriv order admissibleGaussianUnitBumpProfile)) :=
        hprevious.deriv
      exact Eq.subst
        (motive := fun function : ℝ → ℂ =>
          HasCompactSupport function)
        (iteratedDeriv_succ
          (n := order)
          (f := admissibleGaussianUnitBumpProfile)).symm
        hderivative

/-- Every iterated derivative of the fixed bump profile is continuous. -/
theorem admissibleGaussianUnitBumpProfile_iteratedDeriv_continuous
    (order : ℕ) :
    Continuous
      (iteratedDeriv order admissibleGaussianUnitBumpProfile) :=
  admissibleGaussianUnitBumpProfile_contDiff.continuous_iteratedDeriv order
    (naturalOrder_le_contDiffInfinity order)

/-- Every iterated derivative of the fixed bump profile has one positive
global norm bound. -/
theorem exists_admissibleGaussianUnitBumpProfile_iteratedDeriv_norm_bound
    (order : ℕ) :
    ∃ bound : ℝ,
      0 < bound ∧
        ∀ t : ℝ,
          ‖iteratedDeriv order admissibleGaussianUnitBumpProfile t‖ ≤ bound := by
  let derivative : ℝ → ℂ :=
    iteratedDeriv order admissibleGaussianUnitBumpProfile
  have hsupport : HasCompactSupport derivative :=
    admissibleGaussianUnitBumpProfile_iteratedDeriv_hasCompactSupport order
  have hcontinuous : Continuous derivative :=
    admissibleGaussianUnitBumpProfile_iteratedDeriv_continuous order
  have hcompact : IsCompact (tsupport derivative) :=
    hsupport.isCompact
  have hnormContinuous : Continuous (fun t : ℝ => ‖derivative t‖) :=
    continuous_norm.comp hcontinuous
  obtain ⟨rawBound, hrawBound⟩ :=
    hcompact.bddAbove_image hnormContinuous.continuousOn
  let bound : ℝ := max rawBound 0 + 1
  have hboundPositive : 0 < bound :=
    add_pos_of_nonneg_of_pos
      (le_max_right rawBound 0)
      zero_lt_one
  have hinside :
      ∀ t : ℝ,
        t ∈ tsupport derivative →
          ‖derivative t‖ ≤ bound := by
    intro t ht
    have himage :
        ‖derivative t‖ ∈
          (fun u : ℝ => ‖derivative u‖) '' tsupport derivative :=
      Exists.intro t (And.intro ht rfl)
    have hraw : ‖derivative t‖ ≤ rawBound :=
      hrawBound himage
    have hmax : rawBound ≤ max rawBound 0 :=
      le_max_left rawBound 0
    have hincrease : max rawBound 0 ≤ bound :=
      le_add_of_nonneg_right zero_le_one
    exact le_trans hraw (le_trans hmax hincrease)
  have houtside :
      ∀ t : ℝ,
        t ∉ tsupport derivative →
          ‖derivative t‖ ≤ bound := by
    intro t ht
    have hnotSupport : t ∉ Function.support derivative :=
      fun hmembership => ht (subset_tsupport derivative hmembership)
    have hzero : derivative t = 0 :=
      Function.nmem_support.mp hnotSupport
    exact Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ bound)
      hzero.symm
      (Eq.subst
        (motive := fun value : ℝ => value ≤ bound)
        (norm_zero : ‖(0 : ℂ)‖ = 0).symm
        (le_of_lt hboundPositive))
  have hglobal : ∀ t : ℝ, ‖derivative t‖ ≤ bound :=
    fun t => by
      by_cases ht : t ∈ tsupport derivative
      · exact hinside t ht
      · exact houtside t ht
  exact Exists.intro bound (And.intro hboundPositive hglobal)

/-- Scaled fixed bump profiles have derivative bounds uniform over all radii
at least one. -/
theorem exists_admissibleGaussianUnitBumpProfile_div_iteratedDeriv_uniform_bound
    (order : ℕ) :
    ∃ bound : ℝ,
      0 < bound ∧
        ∀ radius : ℝ,
          1 ≤ radius →
            ∀ t : ℝ,
              ‖iteratedDeriv order
                  (fun u : ℝ =>
                    admissibleGaussianUnitBumpProfile (u / radius))
                  t‖ ≤
                bound := by
  obtain ⟨bound, hboundPositive, hbaseBound⟩ :=
    exists_admissibleGaussianUnitBumpProfile_iteratedDeriv_norm_bound order
  have hglobal :
      ∀ radius : ℝ,
        1 ≤ radius →
          ∀ t : ℝ,
            ‖iteratedDeriv order
                (fun u : ℝ =>
                  admissibleGaussianUnitBumpProfile (u / radius))
                t‖ ≤
              bound := by
    intro radius hradius t
    have hradiusPositive : 0 < radius :=
      lt_of_lt_of_le zero_lt_one hradius
    have hinverseNonnegative : 0 ≤ radius⁻¹ :=
      le_of_lt (inv_pos.mpr hradiusPositive)
    have hinverseLeOne : radius⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hradius
    have hinversePowerRaw : radius⁻¹ ^ order ≤ 1 ^ order :=
      pow_le_pow_left₀ hinverseNonnegative hinverseLeOne order
    have hinversePowerLeOne : radius⁻¹ ^ order ≤ 1 :=
      Eq.subst
        (motive := fun right : ℝ => radius⁻¹ ^ order ≤ right)
        (one_pow order)
        hinversePowerRaw
    have hinversePowerNonnegative : 0 ≤ radius⁻¹ ^ order :=
      pow_nonneg hinverseNonnegative order
    have hinversePowerAbsolute : |radius⁻¹ ^ order| = radius⁻¹ ^ order :=
      abs_of_nonneg hinversePowerNonnegative
    have hscaledIdentity :=
      iteratedDeriv_admissibleGaussianUnitBumpProfile_div
        radius order t
    have hnormIdentity :
        ‖radius⁻¹ ^ order •
            iteratedDeriv order admissibleGaussianUnitBumpProfile
              (t / radius)‖ =
          radius⁻¹ ^ order *
            ‖iteratedDeriv order admissibleGaussianUnitBumpProfile
              (t / radius)‖ :=
      Eq.trans
        (norm_smul (radius⁻¹ ^ order)
          (iteratedDeriv order admissibleGaussianUnitBumpProfile
            (t / radius)))
        (congrArg
          (fun value : ℝ => value *
            ‖iteratedDeriv order admissibleGaussianUnitBumpProfile
              (t / radius)‖)
          (Eq.trans
            (Real.norm_eq_abs (radius⁻¹ ^ order))
            hinversePowerAbsolute))
    have hbase := hbaseBound (t / radius)
    have hbaseNonnegative :
        0 ≤ ‖iteratedDeriv order admissibleGaussianUnitBumpProfile
          (t / radius)‖ :=
      norm_nonneg
        (iteratedDeriv order admissibleGaussianUnitBumpProfile
          (t / radius))
    have hscaledBound :
        radius⁻¹ ^ order *
            ‖iteratedDeriv order admissibleGaussianUnitBumpProfile
              (t / radius)‖ ≤
          1 * bound :=
      mul_le_mul
        hinversePowerLeOne
        hbase
        hbaseNonnegative
        zero_le_one
    have hscaledBoundFinal :
        radius⁻¹ ^ order *
            ‖iteratedDeriv order admissibleGaussianUnitBumpProfile
              (t / radius)‖ ≤
          bound :=
      Eq.subst
        (motive := fun right : ℝ =>
          radius⁻¹ ^ order *
              ‖iteratedDeriv order admissibleGaussianUnitBumpProfile
                (t / radius)‖ ≤ right)
        (one_mul bound)
        hscaledBound
    exact Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ bound)
      hscaledIdentity.symm
      (Eq.subst
        (motive := fun left : ℝ => left ≤ bound)
        hnormIdentity.symm
        hscaledBoundFinal)
  exact Exists.intro bound (And.intro hboundPositive hglobal)

/-- The complex-valued standard Gaussian on the real physical line. -/
noncomputable def physicalGaussian (t : ℝ) : ℂ :=
  Complex.exp ((-(t ^ 2) : ℝ) : ℂ)

/-- The standard physical Gaussian is smooth. -/
theorem physicalGaussian_contDiff :
    ContDiff ℝ ∞ physicalGaussian := by
  have hsquare : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2) :=
    (contDiff_id.pow 2)
  have hnegative : ContDiff ℝ ∞ (fun t : ℝ => -(t ^ 2)) :=
    hsquare.neg
  have hcomplex :
      ContDiff ℝ ∞ (fun t : ℝ => (((-(t ^ 2) : ℝ) : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp hnegative
  exact Complex.contDiff_exp.comp hcomplex

/-- The standard physical Gaussian is continuous. -/
theorem physicalGaussian_continuous : Continuous physicalGaussian :=
  physicalGaussian_contDiff.continuous

/-- The norm of the complex physical Gaussian is the real Gaussian. -/
theorem physicalGaussian_norm (t : ℝ) :
    ‖physicalGaussian t‖ = Real.exp (-(t ^ 2)) := by
  have hrealPart : (((-(t ^ 2) : ℝ) : ℂ)).re = -(t ^ 2) :=
    Complex.ofReal_re (-(t ^ 2))
  exact Eq.trans
    (Complex.norm_eq_abs
      (Complex.exp (((-(t ^ 2) : ℝ) : ℂ))))
    (Eq.trans
      (Complex.abs_exp (((-(t ^ 2) : ℝ) : ℂ)))
      (congrArg Real.exp hrealPart))

/-- The norm of the physical Gaussian is integrable. -/
theorem integrable_physicalGaussian_norm :
    MeasureTheory.Integrable (fun t : ℝ => ‖physicalGaussian t‖) := by
  have hrealGaussian :
      MeasureTheory.Integrable
        (fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq zero_lt_one
  have hfunctionEquality :
      (fun t : ℝ => ‖physicalGaussian t‖) =
        (fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2)) := by
    funext t
    have honeProduct : -(1 : ℝ) * t ^ 2 = -(t ^ 2) := by
      exact Eq.trans
        (neg_mul (1 : ℝ) (t ^ 2))
        (congrArg Neg.neg (one_mul (t ^ 2)))
    exact Eq.trans
      (physicalGaussian_norm t)
      (congrArg Real.exp honeProduct.symm)
  exact Eq.subst
    (motive := fun function : ℝ → ℝ =>
      MeasureTheory.Integrable function)
    hfunctionEquality.symm
    hrealGaussian

/-- The compactly supported Gaussian cutoff with inner radius `radius` and
outer radius `2 * radius`. -/
noncomputable def admissibleGaussianCutoff
    (radius : ℝ)
    (hradius : 0 < radius) : ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      ⟨fun t : ℝ =>
          admissibleBump 0 radius (2 * radius)
              hradius
              (lt_two_mul_self hradius) t *
            physicalGaussian t,
        (admissibleBump 0 radius (2 * radius)
          hradius (lt_two_mul_self hradius)).toZetaTestFunction.continuous.mul
            physicalGaussian_continuous⟩
      ((admissibleBump 0 radius (2 * radius)
        hradius (lt_two_mul_self hradius)).hasCompactSupport.mul_right)
  smooth :=
    (admissibleBump_contDiff 0 radius (2 * radius)
      hradius (lt_two_mul_self hradius)).mul
      physicalGaussian_contDiff

/-- Pointwise form of the compact Gaussian cutoff. -/
theorem admissibleGaussianCutoff_apply
    (radius : ℝ)
    (hradius : 0 < radius)
    (t : ℝ) :
    admissibleGaussianCutoff radius hradius t =
      admissibleBump 0 radius (2 * radius)
          hradius (lt_two_mul_self hradius) t *
        physicalGaussian t :=
  Eq.refl _

/-- The radius-dependent bump is the fixed unit bump profile evaluated at the
inverse-radius coordinate. -/
theorem admissibleBump_zero_radius_two_mul_apply_eq_unitProfile
    (radius : ℝ)
    (hradius : 0 < radius)
    (t : ℝ) :
    admissibleBump 0 radius (2 * radius)
        hradius (lt_two_mul_self hradius) t =
      admissibleBump 0 1 2 zero_lt_one one_lt_two (t / radius) := by
  let radiusBump : ContDiffBump (0 : ℝ) :=
    ⟨radius, 2 * radius, hradius, lt_two_mul_self hradius⟩
  let unitBump : ContDiffBump (0 : ℝ) :=
    ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hradiusNonzero : radius ≠ 0 :=
    ne_of_gt hradius
  have hratio : (2 * radius) / radius = (2 : ℝ) := by
    exact Eq.trans
      (mul_div_assoc 2 radius radius)
      (Eq.trans
        (congrArg (fun value : ℝ => 2 * value)
          (div_self hradiusNonzero))
        (mul_one 2))
  have hunitRatio : (2 : ℝ) / 1 = 2 :=
    div_one 2
  have hradiusCoordinate :
      radius⁻¹ • (t - (0 : ℝ)) = t / radius := by
    have hsubtraction : t - (0 : ℝ) = t :=
      sub_zero t
    exact Eq.trans
      (congrArg (fun value : ℝ => radius⁻¹ • value) hsubtraction)
      (Eq.trans
        (Algebra.id.smul_eq_mul (R := ℝ) (radius⁻¹) t)
        (inv_mul_eq_div radius t))
  have hunitCoordinate :
      (1 : ℝ)⁻¹ • (t / radius - (0 : ℝ)) = t / radius := by
    have hsubtraction : t / radius - (0 : ℝ) = t / radius :=
      sub_zero (t / radius)
    exact Eq.trans
      (congrArg (fun value : ℝ => (1 : ℝ)⁻¹ • value) hsubtraction)
      (Eq.trans
        (congrArg (fun scalar : ℝ => scalar • (t / radius)) inv_one)
        (one_smul ℝ (t / radius)))
  change (((radiusBump t : ℝ) : ℂ)) = (((unitBump (t / radius) : ℝ) : ℂ))
  have hradiusApply :
      radiusBump t =
        (someContDiffBumpBase ℝ).toFun
          ((2 * radius) / radius)
          (radius⁻¹ • (t - (0 : ℝ))) :=
    ContDiffBump.apply radiusBump t
  have hunitApply :
      unitBump (t / radius) =
        (someContDiffBumpBase ℝ).toFun
          ((2 : ℝ) / 1)
          ((1 : ℝ)⁻¹ • (t / radius - (0 : ℝ))) :=
    ContDiffBump.apply unitBump (t / radius)
  have hbaseEquality :
      (someContDiffBumpBase ℝ).toFun
          ((2 * radius) / radius)
          (radius⁻¹ • (t - (0 : ℝ))) =
        (someContDiffBumpBase ℝ).toFun
          ((2 : ℝ) / 1)
          ((1 : ℝ)⁻¹ • (t / radius - (0 : ℝ))) :=
    congrArg₂
      (someContDiffBumpBase ℝ).toFun
      (Eq.trans hratio hunitRatio.symm)
      (Eq.trans hradiusCoordinate hunitCoordinate.symm)
  exact congrArg Complex.ofReal
    (Eq.trans hradiusApply
      (Eq.trans hbaseEquality hunitApply.symm))

/-- Every Gaussian cutoff is the product of one fixed bump profile at the
inverse-radius coordinate and the physical Gaussian. -/
theorem admissibleGaussianCutoff_eq_unitProfile_mul_physicalGaussian
    (radius : ℝ)
    (hradius : 0 < radius)
    (t : ℝ) :
    admissibleGaussianCutoff radius hradius t =
      admissibleBump 0 1 2 zero_lt_one one_lt_two (t / radius) *
        physicalGaussian t := by
  exact Eq.trans
    (admissibleGaussianCutoff_apply radius hradius t)
    (congrArg
      (fun value : ℂ => value * physicalGaussian t)
      (admissibleBump_zero_radius_two_mul_apply_eq_unitProfile
        radius hradius t))

/-- On the inner closed ball, the compact Gaussian cutoff equals the Gaussian. -/
theorem admissibleGaussianCutoff_eq_physicalGaussian_of_mem_closedBall
    (radius : ℝ)
    (hradius : 0 < radius)
    (t : ℝ)
    (ht : t ∈ Metric.closedBall (0 : ℝ) radius) :
    admissibleGaussianCutoff radius hradius t = physicalGaussian t := by
  have hbumpOne :
      admissibleBump 0 radius (2 * radius)
          hradius (lt_two_mul_self hradius) t = 1 := by
    change
      (((⟨radius, 2 * radius, hradius, lt_two_mul_self hradius⟩ :
        ContDiffBump (0 : ℝ)) t : ℝ) : ℂ) = 1
    exact complex_ofReal_eq_one_of_real_eq_one
      (ContDiffBump.one_of_mem_closedBall
        (f := (⟨radius, 2 * radius, hradius,
          lt_two_mul_self hradius⟩ : ContDiffBump (0 : ℝ))) ht)
  exact Eq.trans
    (admissibleGaussianCutoff_apply radius hradius t)
    (Eq.trans
      (congrArg (fun value : ℂ => value * physicalGaussian t) hbumpOne)
      (one_mul (physicalGaussian t)))

/-- Outside the outer radius, the compact Gaussian cutoff is zero. -/
theorem admissibleGaussianCutoff_eq_zero_of_outerRadius_le_dist
    (radius : ℝ)
    (hradius : 0 < radius)
    (t : ℝ)
    (ht : 2 * radius ≤ dist t (0 : ℝ)) :
    admissibleGaussianCutoff radius hradius t = 0 := by
  have hbumpZero :
      admissibleBump 0 radius (2 * radius)
          hradius (lt_two_mul_self hradius) t = 0 :=
    admissibleBump_zero_of_le_dist
      0 radius (2 * radius)
      hradius (lt_two_mul_self hradius) ht
  exact Eq.trans
    (admissibleGaussianCutoff_apply radius hradius t)
    (Eq.trans
      (congrArg (fun value : ℂ => value * physicalGaussian t) hbumpZero)
      (zero_mul (physicalGaussian t)))

/-- The canonical natural-radius Gaussian cutoff sequence. -/
noncomputable def admissibleGaussianCutoffNat
    (n : ℕ) : ZetaAdmissibleFunction :=
  admissibleGaussianCutoff ((n : ℝ) + 1)
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)

/-- Pointwise fixed-profile normal form of the natural Gaussian cutoff
sequence. -/
theorem admissibleGaussianCutoffNat_eq_unitProfile_mul_physicalGaussian
    (n : ℕ)
    (t : ℝ) :
    admissibleGaussianCutoffNat n t =
      admissibleBump 0 1 2 zero_lt_one one_lt_two
          (t / ((n : ℝ) + 1)) *
        physicalGaussian t :=
  admissibleGaussianCutoff_eq_unitProfile_mul_physicalGaussian
    ((n : ℝ) + 1)
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)
    t

/-- Every natural-radius cutoff is pointwise bounded by the Gaussian norm. -/
theorem admissibleGaussianCutoffNat_norm_le
    (n : ℕ)
    (t : ℝ) :
    ‖admissibleGaussianCutoffNat n t‖ ≤ ‖physicalGaussian t‖ := by
  let radius : ℝ := (n : ℝ) + 1
  let hradius : 0 < radius :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  let bump : ContDiffBump (0 : ℝ) :=
    ⟨radius, 2 * radius, hradius, lt_two_mul_self hradius⟩
  have hbumpNonnegative : 0 ≤ bump t :=
    ContDiffBump.nonneg bump
  have hbumpLeOne : bump t ≤ 1 :=
    ContDiffBump.le_one bump
  have hbumpAbsolute : |bump t| = bump t :=
    abs_of_nonneg hbumpNonnegative
  have hbumpComplexNorm : ‖((bump t : ℝ) : ℂ)‖ = bump t :=
    Eq.trans
      (Complex.norm_real (bump t))
      (Eq.trans (Real.norm_eq_abs (bump t)) hbumpAbsolute)
  have hproductNorm :
      ‖((bump t : ℝ) : ℂ) * physicalGaussian t‖ =
        bump t * ‖physicalGaussian t‖ :=
    Eq.trans
      (norm_mul (((bump t : ℝ) : ℂ)) (physicalGaussian t))
      (congrArg (fun value : ℝ => value * ‖physicalGaussian t‖)
        hbumpComplexNorm)
  have hbound :
      bump t * ‖physicalGaussian t‖ ≤
        1 * ‖physicalGaussian t‖ :=
    mul_le_mul_of_nonneg_right hbumpLeOne
      (norm_nonneg (physicalGaussian t))
  exact Eq.subst
    (motive := fun left : ℝ => left ≤ ‖physicalGaussian t‖)
    hproductNorm.symm
    (Eq.subst
      (motive := fun right : ℝ =>
        bump t * ‖physicalGaussian t‖ ≤ right)
      (one_mul ‖physicalGaussian t‖)
      hbound)

/-- At every physical point, the natural-radius cutoffs are eventually exactly
the Gaussian. -/
theorem admissibleGaussianCutoffNat_eventually_eq
    (t : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      admissibleGaussianCutoffNat n t = physicalGaussian t := by
  obtain ⟨N, hN⟩ := exists_nat_ge |t|
  exact Filter.eventually_atTop.2
    ⟨N, fun n hn =>
      have hNnReal : (N : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hn
      have htRadius : |t| ≤ (n : ℝ) + 1 :=
        le_trans hN
          (le_trans hNnReal
            (le_add_of_nonneg_right zero_le_one))
      have hdist : dist t (0 : ℝ) = |t| :=
        Eq.trans
          (Real.dist_eq t 0)
          (congrArg abs (sub_zero t))
      have htBall :
          t ∈ Metric.closedBall (0 : ℝ) ((n : ℝ) + 1) :=
        Eq.subst
          (motive := fun value : ℝ => value ≤ (n : ℝ) + 1)
          hdist.symm
          htRadius
      admissibleGaussianCutoff_eq_physicalGaussian_of_mem_closedBall
        ((n : ℝ) + 1)
        (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)
        t
        htBall⟩

/-- The compact Gaussian cutoff integrals converge to the full Gaussian
integral. -/
theorem integral_admissibleGaussianCutoffNat_tendsto_physicalGaussian :
    Filter.Tendsto
      (fun n : ℕ => ∫ t : ℝ, admissibleGaussianCutoffNat n t)
      Filter.atTop
      (nhds (∫ t : ℝ, physicalGaussian t)) := by
  have hmeasurable :
      ∀ n : ℕ,
        MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => admissibleGaussianCutoffNat n t) :=
    fun n =>
      have hcontinuous :
          Continuous
            (fun t : ℝ => admissibleGaussianCutoffNat n t) :=
        (admissibleGaussianCutoffNat n).toZetaTestFunction.continuous
      hcontinuous.aestronglyMeasurable
  have hbound :
      ∀ n : ℕ,
        ∀ᵐ t : ℝ,
          ‖admissibleGaussianCutoffNat n t‖ ≤ ‖physicalGaussian t‖ :=
    fun n => Filter.Eventually.of_forall
      (fun t => admissibleGaussianCutoffNat_norm_le n t)
  have hlimit :
      ∀ᵐ t : ℝ,
        Filter.Tendsto
          (fun n : ℕ => admissibleGaussianCutoffNat n t)
          Filter.atTop
          (nhds (physicalGaussian t)) :=
    Filter.Eventually.of_forall
      (fun t =>
        Filter.Tendsto.congr'
          ((admissibleGaussianCutoffNat_eventually_eq t).mono
            (fun n hn => hn.symm))
          tendsto_const_nhds)
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun t : ℝ => ‖physicalGaussian t‖)
    hmeasurable
    integrable_physicalGaussian_norm
    hbound
    hlimit

/-- At spectral zero, evaluation of a natural Gaussian cutoff is its physical
integral. -/
theorem zetaSpectralEval_admissibleGaussianCutoffNat_zero
    (n : ℕ) :
    zetaSpectralEval (admissibleGaussianCutoffNat n) 0 =
      ∫ t : ℝ, admissibleGaussianCutoffNat n t := by
  have hspectral :=
    zetaSpectralEval_eq_laplace (admissibleGaussianCutoffNat n) 0
  have hintegrand :
      (fun t : ℝ =>
        admissibleGaussianCutoffNat n t *
          Complex.exp ((0 : ℂ) * (t : ℂ))) =
        (fun t : ℝ => admissibleGaussianCutoffNat n t) := by
    funext t
    have hzeroProduct : (0 : ℂ) * (t : ℂ) = 0 :=
      zero_mul (t : ℂ)
    have hexponentialOne : Complex.exp ((0 : ℂ) * (t : ℂ)) = 1 :=
      Eq.trans (congrArg Complex.exp hzeroProduct) Complex.exp_zero
    exact Eq.trans
      (congrArg
        (fun value : ℂ => admissibleGaussianCutoffNat n t * value)
        hexponentialOne)
      (mul_one (admissibleGaussianCutoffNat n t))
  exact Eq.trans hspectral
    (congrArg (fun function : ℝ → ℂ => ∫ t : ℝ, function t) hintegrand)

/-- Spectral values at zero of the compact Gaussian cutoffs converge to the
full Gaussian integral. -/
theorem zetaSpectralEval_admissibleGaussianCutoffNat_zero_tendsto :
    Filter.Tendsto
      (fun n : ℕ => zetaSpectralEval (admissibleGaussianCutoffNat n) 0)
      Filter.atTop
      (nhds (∫ t : ℝ, physicalGaussian t)) :=
  Filter.Tendsto.congr'
    (Filter.Eventually.of_forall
      (fun n =>
        (zetaSpectralEval_admissibleGaussianCutoffNat_zero n).symm))
    integral_admissibleGaussianCutoffNat_tendsto_physicalGaussian

/-- The full physical Gaussian integral has the standard complex Gaussian
value. -/
theorem integral_physicalGaussian_eq :
    (∫ t : ℝ, physicalGaussian t) =
      ((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ) := by
  have hgaussian :=
    integral_gaussian_complex
      (b := (1 : ℂ))
      (show 0 < (1 : ℂ).re from zero_lt_one)
  have hintegrand :
      (fun t : ℝ => physicalGaussian t) =
        (fun t : ℝ => Complex.exp (-((1 : ℂ)) * (t : ℂ) ^ 2)) := by
    funext t
    have hpowerCast : ((t : ℂ) ^ 2) = ((t ^ 2 : ℝ) : ℂ) :=
      (Complex.ofReal_pow t 2).symm
    have hargument :
        -((1 : ℂ)) * (t : ℂ) ^ 2 = (((-(t ^ 2) : ℝ) : ℂ)) := by
      calc
        -((1 : ℂ)) * (t : ℂ) ^ 2 = -((t : ℂ) ^ 2) :=
          neg_one_mul ((t : ℂ) ^ 2)
        _ = -(((t ^ 2 : ℝ) : ℂ)) :=
          congrArg Neg.neg hpowerCast
        _ = (((-(t ^ 2) : ℝ) : ℂ)) :=
          (Complex.ofReal_neg (t ^ 2)).symm
    exact congrArg Complex.exp hargument.symm
  exact Eq.trans
    (congrArg (fun function : ℝ → ℂ => ∫ t : ℝ, function t) hintegrand)
    hgaussian

/-- The full physical Gaussian integral is nonzero. -/
theorem integral_physicalGaussian_ne_zero :
    (∫ t : ℝ, physicalGaussian t) ≠ 0 := by
  have hbase : ((Real.pi : ℂ) / (1 : ℂ)) ≠ 0 :=
    div_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      one_ne_zero
  have hpower :
      ((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro hzero
    have hzeroCharacterization :
        ((Real.pi : ℂ) / (1 : ℂ)) = 0 ∧ (1 / 2 : ℂ) ≠ 0 :=
      (Complex.cpow_eq_zero_iff
        ((Real.pi : ℂ) / (1 : ℂ)) (1 / 2 : ℂ)).mp hzero
    have hbaseZero : ((Real.pi : ℂ) / (1 : ℂ)) = 0 :=
      hzeroCharacterization.1
    exact hbase hbaseZero
  exact Eq.subst
    (motive := fun value : ℂ => value ≠ 0)
    integral_physicalGaussian_eq.symm
    hpower

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
