import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.KernelEnvelope
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.UpperHalfStripGeometry

/-!
# Algebraic upper-half-strip normalizer

The exponential normalizer used by the finite-order PL owner cannot yield a
polynomial conclusion.  This file owns the elementary algebraic normalizer
needed for the polynomial route.  Its zero is placed below the upper tail.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

def verticalStripAlgebraicNormalizer
    (R : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (z + (R : ℂ) * Complex.I) ^ N

def verticalStripAlgebraicallyNormalized
    (f : ℂ → ℂ) (R : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  f z / verticalStripAlgebraicNormalizer R N z

/-! The PL normalizer must be holomorphic on the *whole* open strip.  A zero
of the upper-tail normalizer would otherwise sit inside that domain. -/

def verticalStripLeftAlgebraicNormalizer
    (a : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (z - ((a - 1 : ℝ) : ℂ)) ^ N

def verticalStripLeftAlgebraicallyNormalized
    (f : ℂ → ℂ) (a : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  f z / verticalStripLeftAlgebraicNormalizer a N z

theorem verticalStripLeftAlgebraicNormalizer_ne_zero
    {a : ℝ} {N : ℕ} {z : ℂ}
    (hza : a < z.re) :
    verticalStripLeftAlgebraicNormalizer a N z ≠ 0 := by
  have hre : 0 < (z - ((a - 1 : ℝ) : ℂ)).re := by
    calc
      0 < z.re - (a - 1) := by
        exact sub_pos.mpr (lt_trans (sub_lt_self a zero_lt_one) hza)
      _ = (z - ((a - 1 : ℝ) : ℂ)).re := by
        exact (Complex.sub_re z ((a - 1 : ℝ) : ℂ)).symm.trans
          (congrArg (fun u : ℝ => z.re - u) (Complex.ofReal_re (a - 1)))
  exact pow_ne_zero N (by
    intro hzero
    have := congrArg Complex.re hzero
    exact (ne_of_gt hre) this)

theorem verticalStripLeftAlgebraicNormalizer_norm_upper_bound
    {a : ℝ} {N : ℕ} {z : ℂ} :
    ‖verticalStripLeftAlgebraicNormalizer a N z‖ ≤
      (‖z‖ + |a - 1|) ^ N := by
  have hbase :
      ‖z - ((a - 1 : ℝ) : ℂ)‖ ≤ ‖z‖ + |a - 1| := by
    have htriangle := norm_sub_le z ((a - 1 : ℝ) : ℂ)
    have hreal : ‖((a - 1 : ℝ) : ℂ)‖ = |a - 1| :=
      norm_real (a - 1)
    exact Eq.subst
      (motive := fun u : ℝ => ‖z - ((a - 1 : ℝ) : ℂ)‖ ≤ ‖z‖ + u)
      hreal.symm htriangle
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hbase N
  exact Eq.subst
    (motive := fun u : ℝ => ‖verticalStripLeftAlgebraicNormalizer a N z‖ ≤ u)
    (norm_pow (z - ((a - 1 : ℝ) : ℂ)) N)
    hpow

theorem verticalStripLeftAlgebraicallyNormalized_norm_upper_bound_of_raw
    (f : ℂ → ℂ) {a C : ℝ} {N : ℕ} {z : ℂ}
    (hz : 0 < z.im)
    (hraw : ‖f z‖ ≤ C) :
    ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤
      C * z.im⁻¹ ^ N := by
  have him : (z - ((a - 1 : ℝ) : ℂ)).im = z.im := by
    calc
      (z - ((a - 1 : ℝ) : ℂ)).im = z.im - ((a - 1 : ℝ) : ℂ).im := by
        exact Complex.sub_im z ((a - 1 : ℝ) : ℂ)
      _ = z.im := by
        exact congrArg (fun u : ℝ => z.im - u) (Complex.ofReal_im (a - 1))
  have him_nonneg : 0 ≤ (z - ((a - 1 : ℝ) : ℂ)).im :=
    him.symm ▸ hz
  have hbase : z.im ≤ ‖z - ((a - 1 : ℝ) : ℂ)‖ := by
    calc
      z.im = ‖(z - ((a - 1 : ℝ) : ℂ)).im‖ :=
        (norm_of_nonneg him_nonneg).symm.trans him.symm
      _ ≤ ‖z - ((a - 1 : ℝ) : ℂ)‖ :=
        Complex.norm_im_le_norm _
  have hpow : z.im ^ N ≤
      ‖verticalStripLeftAlgebraicNormalizer a N z‖ := by
    have := pow_le_pow_left₀ (le_of_lt hz) hbase N
    exact Eq.subst
      (motive := fun u : ℝ => z.im ^ N ≤ u)
      (norm_pow (z - ((a - 1 : ℝ) : ℂ)) N)
      this
  have hnorm : 0 ≤ ‖f z‖ := norm_nonneg _
  have hC : 0 ≤ C := le_trans hnorm hraw
  have hmul : ‖f z‖ * ‖verticalStripLeftAlgebraicNormalizer a N z‖⁻¹ ≤
      C * (z.im ^ N)⁻¹ := by
    exact mul_le_mul hraw
      (inv_anti₀ (pow_pos hz N) hpow)
      (norm_nonneg _) hC
  unfold verticalStripLeftAlgebraicallyNormalized
  calc
    ‖f z / verticalStripLeftAlgebraicNormalizer a N z‖ =
        ‖f z‖ * ‖verticalStripLeftAlgebraicNormalizer a N z‖⁻¹ := by
      exact norm_div _ _
    _ ≤ C * (z.im ^ N)⁻¹ := hmul
    _ = C * z.im⁻¹ ^ N := by
      exact congrArg (fun u : ℝ => C * u) (inv_pow z.im N)

theorem verticalStripLeftAlgebraicNormalizer_undamps_bound
    (f : ℂ → ℂ) {a : ℝ} {N : ℕ} {z : ℂ}
    (hza : a ≤ z.re)
    (hbound :
      ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ 1) :
    ‖f z‖ ≤ (‖z‖ + |a - 1|) ^ N := by
  have hstrict : a - 1 < z.re :=
    lt_of_lt_of_le (sub_lt_self a zero_lt_one) hza
  have hdenom := verticalStripLeftAlgebraicNormalizer_ne_zero hstrict
  have hreconstruct :
      f z = verticalStripLeftAlgebraicallyNormalized f a N z *
        verticalStripLeftAlgebraicNormalizer a N z := by
    unfold verticalStripLeftAlgebraicallyNormalized
    exact (div_mul_cancel₀ (f z) hdenom).symm
  have hnorm := congrArg norm hreconstruct
  have hproduct :
      ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ *
          ‖verticalStripLeftAlgebraicNormalizer a N z‖ ≤
        1 * (‖z‖ + |a - 1|) ^ N :=
    mul_le_mul hbound
      (verticalStripLeftAlgebraicNormalizer_norm_upper_bound)
      (norm_nonneg _) zero_le_one
  calc
    ‖f z‖ = ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ *
        ‖verticalStripLeftAlgebraicNormalizer a N z‖ := hnorm
    _ ≤ 1 * (‖z‖ + |a - 1|) ^ N := hproduct
    _ = (‖z‖ + |a - 1|) ^ N := one_mul _

theorem differentiable_verticalStripLeftAlgebraicNormalizer
    (a : ℝ) (N : ℕ) :
    Differentiable ℂ (verticalStripLeftAlgebraicNormalizer a N) := by
  exact
    (differentiable_id.sub
      (differentiable_const (c := ((a - 1 : ℝ) : ℂ)))).pow N

theorem verticalStripLeftAlgebraicallyNormalized_diffContOnCl_of_differentiable
    (f : ℂ → ℂ) {a b : ℝ} {N : ℕ}
    (hf : Differentiable ℂ f) :
    DiffContOnCl ℂ
      (verticalStripLeftAlgebraicallyNormalized f a N)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  apply DifferentiableOn.diffContOnCl
  exact (hf.differentiableOn.div
    (differentiable_verticalStripLeftAlgebraicNormalizer a N).differentiableOn
    (fun z hz => verticalStripLeftAlgebraicNormalizer_ne_zero hz.1))

theorem verticalStripLeftAlgebraicallyNormalized_polynomial_PL_transport
    (f : ℂ → ℂ) {a b C : ℝ} {N : ℕ}
    (hab : a < b)
    (hhol : DiffContOnCl ℂ
      (verticalStripLeftAlgebraicallyNormalized f a N)
      (Complex.re ⁻¹' Set.Ioo a b))
    (hbottom :
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C)
    (hleft :
      ∀ z : ℂ, z.re = a → 1 ≤ z.im →
        ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C)
    (hright :
      ∀ z : ℂ, z.re = b → 1 ≤ z.im →
        ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C)
    (htop :
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z.im = R →
          ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ z.im →
      ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C := by
  exact verticalStripUpperHalfStrip_norm_le_of_eventual_top_boundary
    (verticalStripLeftAlgebraicallyNormalized f a N) hab
    hhol
    hbottom hleft hright htop

theorem verticalStripLeftAlgebraicNormalizer_polynomial_strip_bound
    (f : ℂ → ℂ) {a b C : ℝ} {N : ℕ}
    (hab : a < b)
    (hhol : DiffContOnCl ℂ
      (verticalStripLeftAlgebraicallyNormalized f a N)
      (Complex.re ⁻¹' Set.Ioo a b))
    (hbottom :
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C)
    (hleft :
      ∀ z : ℂ, z.re = a → 1 ≤ z.im →
        ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C)
    (hright :
      ∀ z : ℂ, z.re = b → 1 ≤ z.im →
        ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C)
    (htop :
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z.im = R →
          ‖verticalStripLeftAlgebraicallyNormalized f a N z‖ ≤ C) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ z.im →
      ‖f z‖ ≤ (‖z‖ + |a - 1|) ^ N := by
  have hnormalized :=
    verticalStripLeftAlgebraicallyNormalized_polynomial_PL_transport f hab hhol
      hbottom hleft hright htop
  exact fun z hza hzb hz =>
    verticalStripLeftAlgebraicNormalizer_undamps_bound f hza
      (hnormalized z hza hzb hz)

theorem differentiable_verticalStripAlgebraicNormalizer
    (R : ℝ) (N : ℕ) :
    Differentiable ℂ (verticalStripAlgebraicNormalizer R N) := by
  exact
    (differentiable_id.add
      (differentiable_const.mul differentiable_const)).pow N

theorem verticalStripAlgebraicNormalizer_im
    (R : ℝ) (z : ℂ) :
    (z + (R : ℂ) * Complex.I).im = z.im + R := by
    calc
      (z + (R : ℂ) * Complex.I).im = z.im + ((R : ℂ) * Complex.I).im := by
      exact Complex.add_im z ((R : ℂ) * Complex.I)
    _ = z.im + ((R : ℂ).re * Complex.I.im +
          (R : ℂ).im * Complex.I.re) := by
      exact congrArg (fun u : ℝ => z.im + u)
        (Complex.mul_im (R : ℂ) Complex.I)
    _ = z.im + R := by
      calc
        z.im + ((R : ℂ).re * Complex.I.im +
            (R : ℂ).im * Complex.I.re) =
            z.im + (R * 1 + 0 * 0) := by
          exact congrArg (fun u : ℝ => z.im + u)
            (congrArg₂ HAdd.hAdd
            (congrArg₂ (fun a b : ℝ => a * b)
              (Complex.ofReal_re R) Complex.I.im)
              (congrArg₂ (fun a b : ℝ => a * b)
                (Complex.ofReal_im R) Complex.I.re))
        _ = z.im + R := by
          exact congrArg (fun u : ℝ => z.im + u)
            (Eq.trans (add_zero (R * 1)) (mul_one R))

theorem verticalStripAlgebraicNormalizer_ne_zero
    {R : ℝ} {z : ℂ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im) :
    z + (R : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have him_zero : (z + (R : ℂ) * Complex.I).im = 0 := by
    exact congrArg Complex.im hzero
  have him_value : z.im + R = 0 := by
    exact (verticalStripAlgebraicNormalizer_im R z).symm.trans him_zero
  have hpositive : 0 < z.im + R :=
    add_pos_of_nonneg_of_pos hz hR
  exact (ne_of_gt hpositive) him_value

theorem verticalStripAlgebraicNormalizer_pow_ne_zero
    {R : ℝ} {N : ℕ} {z : ℂ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im) :
    verticalStripAlgebraicNormalizer R N z ≠ 0 := by
  exact pow_ne_zero N (verticalStripAlgebraicNormalizer_ne_zero hR hz)

theorem differentiableOn_verticalStripAlgebraicallyNormalized_upperTail
    (f : ℂ → ℂ)
    (R : ℝ) (N : ℕ)
    (hf : Differentiable ℂ f)
    (hR : 0 < R) :
    DifferentiableOn ℂ
      (verticalStripAlgebraicallyNormalized f R N)
      {z : ℂ | 0 ≤ z.im} := by
  exact DifferentiableOn.div
    hf.differentiableOn
    (differentiable_verticalStripAlgebraicNormalizer R N).differentiableOn
    (fun z hz => verticalStripAlgebraicNormalizer_pow_ne_zero hR hz)

theorem verticalStripAlgebraicNormalizer_norm_lower_bound
    {R : ℝ} {z : ℂ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im) :
    R + z.im ≤ ‖z + (R : ℂ) * Complex.I‖ := by
  have hheight : 0 ≤ R + z.im :=
    le_of_lt (add_pos_of_nonneg_of_pos hz hR)
  have him_nonneg : 0 ≤ (z + (R : ℂ) * Complex.I).im := by
    exact (verticalStripAlgebraicNormalizer_im R z).symm ▸ hheight
  have him_norm : ‖(z + (R : ℂ) * Complex.I).im‖ = R + z.im := by
    calc
      ‖(z + (R : ℂ) * Complex.I).im‖ =
          (z + (R : ℂ) * Complex.I).im := norm_of_nonneg him_nonneg
      _ = R + z.im := verticalStripAlgebraicNormalizer_im R z
  have him_le : ‖(z + (R : ℂ) * Complex.I).im‖ ≤
      ‖z + (R : ℂ) * Complex.I‖ :=
    Complex.norm_im_le_norm (z + (R : ℂ) * Complex.I)
  exact le_trans (le_of_eq him_norm.symm) him_le

theorem verticalStripAlgebraicNormalizer_norm_lower_bound_pow
    {R : ℝ} {N : ℕ} {z : ℂ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im) :
    (R + z.im) ^ N ≤
      ‖verticalStripAlgebraicNormalizer R N z‖ := by
  have hbase : 0 ≤ R + z.im :=
    le_of_lt (add_pos_of_nonneg_of_pos hz hR)
  have hpow := pow_le_pow_left₀ hbase
    (verticalStripAlgebraicNormalizer_norm_lower_bound hR hz) N
  exact Eq.subst
    (motive := fun u : ℝ => (R + z.im) ^ N ≤ u)
    (norm_pow (z + (R : ℂ) * Complex.I) N)
    hpow

theorem verticalStripAlgebraicNormalizer_inv_norm_upper_bound
    {R : ℝ} {N : ℕ} {z : ℂ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im) :
    ‖(verticalStripAlgebraicNormalizer R N z)⁻¹‖ ≤
      (R + z.im)⁻¹ ^ N := by
  have hbase_pos : 0 < R + z.im :=
    add_pos_of_nonneg_of_pos hz hR
  have hpow_pos : 0 < (R + z.im) ^ N :=
    pow_pos hbase_pos N
  have hnorm_lower :=
    verticalStripAlgebraicNormalizer_norm_lower_bound_pow hR hz
  have hinv :
      ‖verticalStripAlgebraicNormalizer R N z‖⁻¹ ≤
        ((R + z.im) ^ N)⁻¹ :=
    inv_anti₀ hpow_pos hnorm_lower
  calc
    ‖(verticalStripAlgebraicNormalizer R N z)⁻¹‖ =
        ‖verticalStripAlgebraicNormalizer R N z‖⁻¹ :=
      norm_inv _
    _ ≤ ((R + z.im) ^ N)⁻¹ := hinv
    _ = (R + z.im)⁻¹ ^ N := inv_pow (R + z.im) N

theorem verticalStripAlgebraicallyNormalized_norm_upper_bound
    (f : ℂ → ℂ)
    {R : ℝ} {N : ℕ} {z : ℂ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im) :
    ‖verticalStripAlgebraicallyNormalized f R N z‖ ≤
      ‖f z‖ * (R + z.im)⁻¹ ^ N := by
  have hinv := verticalStripAlgebraicNormalizer_inv_norm_upper_bound hR hz
  have hnorm_f : 0 ≤ ‖f z‖ := norm_nonneg (f z)
  have hmul := mul_le_mul_of_nonneg_left hinv hnorm_f
  unfold verticalStripAlgebraicallyNormalized
  calc
    ‖f z / verticalStripAlgebraicNormalizer R N z‖ =
        ‖f z‖ * ‖(verticalStripAlgebraicNormalizer R N z)⁻¹‖ := by
      exact norm_div (f z) (verticalStripAlgebraicNormalizer R N z)
    _ ≤ ‖f z‖ * (R + z.im)⁻¹ ^ N := hmul

theorem verticalStripAlgebraicNormalizer_norm_upper_bound
    {R : ℝ} {N : ℕ} {z : ℂ} :
    0 ≤ R →
    ‖verticalStripAlgebraicNormalizer R N z‖ ≤
      (‖z‖ + R) ^ N := by
  intro hR
  have hbase :
      ‖z + (R : ℂ) * Complex.I‖ ≤ ‖z‖ + R := by
    have htriangle :
        ‖z + (R : ℂ) * Complex.I‖ ≤
          ‖z‖ + ‖(R : ℂ) * Complex.I‖ :=
      norm_add_le z ((R : ℂ) * Complex.I)
    have hscalar : ‖(R : ℂ) * Complex.I‖ = |R| := by
      calc
        ‖(R : ℂ) * Complex.I‖ = ‖(R : ℂ)‖ * ‖Complex.I‖ :=
          norm_mul _ _
        _ = |R| := by
          exact congrArg (fun u : ℝ => u * 1) (norm_real R)
    have hbase' : ‖z + (R : ℂ) * Complex.I‖ ≤ ‖z‖ + |R| := by
      exact Eq.subst
        (motive := fun u : ℝ => ‖z + (R : ℂ) * Complex.I‖ ≤ ‖z‖ + u)
        hscalar.symm htriangle
    exact le_trans hbase'
      (add_le_add_left (abs_of_nonneg hR) ‖z‖)
  have hpow_nonneg : 0 ≤ ‖z + (R : ℂ) * Complex.I‖ :=
    norm_nonneg _
  have hpow := pow_le_pow_left₀ hpow_nonneg hbase N
  exact Eq.subst
    (motive := fun u : ℝ =>
      ‖verticalStripAlgebraicNormalizer R N z‖ ≤ u)
    (norm_pow (z + (R : ℂ) * Complex.I) N)
    hpow

theorem verticalStripAlgebraicNormalizer_undamps_bound
    (f : ℂ → ℂ)
    {R : ℝ} {N : ℕ} {z : ℂ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im)
    (hbound :
      ‖verticalStripAlgebraicallyNormalized f R N z‖ ≤ 1) :
    ‖f z‖ ≤ (‖z‖ + R) ^ N := by
  have hdenom_ne_zero := verticalStripAlgebraicNormalizer_pow_ne_zero hR hz
  have hreconstruct :
      f z =
        verticalStripAlgebraicallyNormalized f R N z *
          verticalStripAlgebraicNormalizer R N z := by
    unfold verticalStripAlgebraicallyNormalized
    exact (div_mul_cancel₀ (f z) hdenom_ne_zero).symm
  have hnorm_product :
      ‖f z‖ =
        ‖verticalStripAlgebraicallyNormalized f R N z‖ *
          ‖verticalStripAlgebraicNormalizer R N z‖ := by
    exact congrArg norm hreconstruct
  have hnorm_le :
      ‖verticalStripAlgebraicallyNormalized f R N z‖ *
          ‖verticalStripAlgebraicNormalizer R N z‖ ≤
        1 * (‖z‖ + R) ^ N := by
    exact mul_le_mul
      hbound
      (verticalStripAlgebraicNormalizer_norm_upper_bound (le_of_lt hR))
      (norm_nonneg _)
      zero_le_one
  calc
    ‖f z‖ =
        ‖verticalStripAlgebraicallyNormalized f R N z‖ *
          ‖verticalStripAlgebraicNormalizer R N z‖ := hnorm_product
    _ ≤ 1 * (‖z‖ + R) ^ N := hnorm_le
    _ = (‖z‖ + R) ^ N := one_mul _

theorem verticalStripAlgebraicNormalizer_undamps_bound_of_uniform_bound
    (f : ℂ → ℂ)
    {R : ℝ} {N : ℕ} {z : ℂ} {M : ℝ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im)
    (hM : 0 ≤ M)
    (hbound :
      ‖verticalStripAlgebraicallyNormalized f R N z‖ ≤ M) :
    ‖f z‖ ≤ M * (‖z‖ + R) ^ N := by
  have hdenom_ne_zero := verticalStripAlgebraicNormalizer_pow_ne_zero hR hz
  have hreconstruct :
      f z =
        verticalStripAlgebraicallyNormalized f R N z *
          verticalStripAlgebraicNormalizer R N z := by
    unfold verticalStripAlgebraicallyNormalized
    exact (div_mul_cancel₀ (f z) hdenom_ne_zero).symm
  have hnorm_product :
      ‖f z‖ =
        ‖verticalStripAlgebraicallyNormalized f R N z‖ *
          ‖verticalStripAlgebraicNormalizer R N z‖ :=
    congrArg norm hreconstruct
  have hnormalizer :=
    verticalStripAlgebraicNormalizer_norm_upper_bound (le_of_lt hR)
  have hproduct :
      ‖verticalStripAlgebraicallyNormalized f R N z‖ *
          ‖verticalStripAlgebraicNormalizer R N z‖ ≤
        M * (‖z‖ + R) ^ N := by
    exact mul_le_mul hbound hnormalizer
      (norm_nonneg _)
      hM
  exact hnorm_product ▸ hproduct

theorem verticalStripAlgebraicallyNormalized_boundary_decay_of_polynomial_bound
    (f : ℂ → ℂ)
    {R : ℝ} {m : ℕ} {z : ℂ} {A : ℝ}
    (hR : 0 < R)
    (hz : 0 ≤ z.im)
    (hA : 0 ≤ A)
    (hboundary :
      ‖f z‖ ≤ A * (R + z.im) ^ m) :
    ‖verticalStripAlgebraicallyNormalized f R (m + 1) z‖ ≤
      A * (R + z.im) ^ m * (R + z.im)⁻¹ ^ (m + 1) := by
  have hbase_pos : 0 < R + z.im :=
    add_pos_of_nonneg_of_pos hz hR
  have hinvpow_pos : 0 < (R + z.im)⁻¹ ^ (m + 1) :=
    pow_pos (inv_pos.mpr hbase_pos) (m + 1)
  have hcombined :
      ‖f z‖ * (R + z.im)⁻¹ ^ (m + 1) ≤
        (A * (R + z.im) ^ m) * (R + z.im)⁻¹ ^ (m + 1) := by
    exact mul_le_mul_of_nonneg_right hboundary
      (le_of_lt hinvpow_pos)
  calc
    ‖verticalStripAlgebraicallyNormalized f R (m + 1) z‖ ≤
        ‖f z‖ * (R + z.im)⁻¹ ^ (m + 1) :=
      verticalStripAlgebraicallyNormalized_norm_upper_bound f hR hz
    _ ≤ (A * (R + z.im) ^ m) * (R + z.im)⁻¹ ^ (m + 1) :=
      hcombined

end
end LFunctions
end Boundary
