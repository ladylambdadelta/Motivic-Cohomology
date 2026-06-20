import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.SupportEnvelope.Owner

/-!
# Paley-Wiener rectangle algebra

This file owns the real rectangle/corner algebra and the complex exponential
coordinate lemmas used by the Paley-Wiener decay package. It is copy-first
extracted from the current Paley-Wiener owner file and is not imported by that
parent yet, so declaration names intentionally match the existing owner
surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- Absolute value on an interval is bounded by the larger endpoint absolute value. -/
theorem abs_le_max_abs_endpoints_of_mem_interval
    (a b x : ℝ) (hxa : a ≤ x) (hxb : x ≤ b) :
    |x| ≤ max |a| |b| := by
  have hx_upper : x ≤ max |a| |b| :=
    le_trans hxb
      (le_trans (le_abs_self b) (le_max_right |a| |b|))
  have hx_neg_upper : -x ≤ max |a| |b| :=
    le_trans (neg_le_neg hxa)
      (le_trans (neg_le_abs a) (le_max_left |a| |b|))
  have hx_lower : -(max |a| |b|) ≤ x :=
    neg_le.mp hx_neg_upper
  exact abs_le.mpr ⟨hx_lower, hx_upper⟩

/-- The product of the one-dimensional endpoint absolute-value envelopes dominates the
rectangle product. -/
theorem abs_mul_le_endpointEnvelopeProduct_of_mem_interval
    (a b lower upper x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : lower ≤ t) (ht_upper : t ≤ upper) :
    |x * t| ≤ max |a| |b| * max |lower| |upper| := by
  have hx : |x| ≤ max |a| |b| :=
    abs_le_max_abs_endpoints_of_mem_interval a b x hxa hxb
  have ht : |t| ≤ max |lower| |upper| :=
    abs_le_max_abs_endpoints_of_mem_interval lower upper t ht_lower ht_upper
  have hendpoint_nonneg : 0 ≤ max |a| |b| :=
    le_max_of_le_left (abs_nonneg a)
  have hmul :
      |x| * |t| ≤ max |a| |b| * max |lower| |upper| :=
    mul_le_mul hx ht (abs_nonneg t) hendpoint_nonneg
  exact Eq.subst
    (motive := fun v : ℝ => v ≤ max |a| |b| * max |lower| |upper|)
    (abs_mul x t).symm
    hmul

/-- The product of nonnegative max envelopes bounds each of the four products. -/
theorem four_products_le_max_mul_max_of_nonneg
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    max (max (a * c) (a * d)) (max (b * c) (b * d)) ≤
      max a b * max c d := by
  have hmaxab_nonneg : 0 ≤ max a b :=
    le_max_of_le_left ha
  have hac : a * c ≤ max a b * max c d :=
    mul_le_mul (le_max_left a b) (le_max_left c d) hc hmaxab_nonneg
  have had : a * d ≤ max a b * max c d :=
    mul_le_mul (le_max_left a b) (le_max_right c d) hd hmaxab_nonneg
  have hbc : b * c ≤ max a b * max c d :=
    mul_le_mul (le_max_right a b) (le_max_left c d) hc hmaxab_nonneg
  have hbd : b * d ≤ max a b * max c d :=
    mul_le_mul (le_max_right a b) (le_max_right c d) hd hmaxab_nonneg
  exact max_le (max_le hac had) (max_le hbc hbd)

/-- The first corner product is included in the four-product maximum. -/
theorem first_product_le_four_products
    (a b c d : ℝ) :
    a * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_left (a * c) (a * d))
    (le_max_left (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The second corner product is included in the four-product maximum. -/
theorem second_product_le_four_products
    (a b c d : ℝ) :
    a * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_right (a * c) (a * d))
    (le_max_left (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The third corner product is included in the four-product maximum. -/
theorem third_product_le_four_products
    (a b c d : ℝ) :
    b * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_left (b * c) (b * d))
    (le_max_right (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The fourth corner product is included in the four-product maximum. -/
theorem fourth_product_le_four_products
    (a b c d : ℝ) :
    b * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_right (b * c) (b * d))
    (le_max_right (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The product of nonnegative max envelopes is bounded by the four-product maximum. -/
theorem max_mul_max_le_four_products_of_nonneg
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    max a b * max c d ≤
      max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  by_cases hab : a ≤ b
  · have hmaxab : max a b = b := max_eq_right hab
    by_cases hcd : c ≤ d
    · have hmaxcd : max c d = d := max_eq_right hcd
      have hcorner :
          b * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        fourth_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            b * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)
    · have hdc : d ≤ c := le_of_not_ge hcd
      have hmaxcd : max c d = c := max_eq_left hdc
      have hcorner :
          b * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        third_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            b * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)
  · have hba : b ≤ a := le_of_not_ge hab
    have hmaxab : max a b = a := max_eq_left hba
    by_cases hcd : c ≤ d
    · have hmaxcd : max c d = d := max_eq_right hcd
      have hcorner :
          a * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        second_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            a * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)
    · have hdc : d ≤ c := le_of_not_ge hcd
      have hmaxcd : max c d = c := max_eq_left hdc
      have hcorner :
          a * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        first_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            a * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)

/-- Multiplying two nonnegative two-point max envelopes gives the max of the four products. -/
theorem max_mul_max_of_nonneg_eq_max_four_products
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    max a b * max c d =
      max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  exact le_antisymm
    (max_mul_max_le_four_products_of_nonneg ha hb hc hd)
    (four_products_le_max_mul_max_of_nonneg ha hb hc hd)

/-- Absolute value of a product as separated absolute-value factors. -/
theorem abs_mul_eq_abs_mul_abs
    (x y : ℝ) :
    |x * y| = |x| * |y| := by
  exact abs_mul x y

/-- The four-corner max written with separated absolute-value products equals the corner
absolute-product max. -/
theorem max_four_abs_products_eq_max_corner_abs
    (a b lower upper : ℝ) :
    max (max (|a| * |lower|) (|a| * |upper|))
        (max (|b| * |lower|) (|b| * |upper|)) =
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  exact congrArg₂ max
    (congrArg₂ max
      (abs_mul_eq_abs_mul_abs a lower).symm
      (abs_mul_eq_abs_mul_abs a upper).symm)
    (congrArg₂ max
      (abs_mul_eq_abs_mul_abs b lower).symm
      (abs_mul_eq_abs_mul_abs b upper).symm)

/-- The product of the one-dimensional absolute endpoint envelopes is the maximum of the
four corner absolute products. -/
theorem max_abs_mul_max_abs_eq_max_corner_abs
    (a b lower upper : ℝ) :
    max |a| |b| * max |lower| |upper| =
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  have hmax :
      max |a| |b| * max |lower| |upper| =
        max (max (|a| * |lower|) (|a| * |upper|))
          (max (|b| * |lower|) (|b| * |upper|)) :=
    max_mul_max_of_nonneg_eq_max_four_products
      (abs_nonneg a)
      (abs_nonneg b)
      (abs_nonneg lower)
      (abs_nonneg upper)
  exact Eq.trans hmax (max_four_abs_products_eq_max_corner_abs a b lower upper)

/-- The product of endpoint absolute-value envelopes is bounded by the four-corner
absolute-value envelope. -/
theorem endpointEnvelopeProduct_le_max_corner_abs
    (a b lower upper : ℝ) :
    max |a| |b| * max |lower| |upper| ≤
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  exact le_of_eq (max_abs_mul_max_abs_eq_max_corner_abs a b lower upper)

/-- A rectangle product is bounded in absolute value by the largest absolute product at
the four corners. -/
theorem abs_mul_le_max_corner_abs_of_mem_interval
    (a b lower upper x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : lower ≤ t) (ht_upper : t ≤ upper) :
    |x * t| ≤
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  have hproduct :
      |x * t| ≤ max |a| |b| * max |lower| |upper| :=
    abs_mul_le_endpointEnvelopeProduct_of_mem_interval
      a b lower upper x t hxa hxb ht_lower ht_upper
  have hcorner :
      max |a| |b| * max |lower| |upper| ≤
        max (max (|a * lower|) (|a * upper|))
          (max (|b * lower|) (|b * upper|)) :=
    endpointEnvelopeProduct_le_max_corner_abs a b lower upper
  exact le_trans hproduct hcorner

/-- The unsigned rectangle product is bounded by the corner absolute-value envelope. -/
theorem mul_le_max_corner_abs_of_mem_interval
    (a b lower upper x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : lower ≤ t) (ht_upper : t ≤ upper) :
    x * t ≤
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  have hle_abs : x * t ≤ |x * t| :=
    le_abs_self (x * t)
  have habs :
      |x * t| ≤
        max (max (|a * lower|) (|a * upper|))
          (max (|b * lower|) (|b * upper|)) :=
    abs_mul_le_max_corner_abs_of_mem_interval
      a b lower upper x t hxa hxb ht_lower ht_upper
  exact le_trans hle_abs habs

/-- The real exponent `x * t` is bounded by the endpoint envelope on the strip rectangle. -/
theorem zetaPaleyWienerStripProduct_le_endpointEnvelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : I.lower ≤ t) (ht_upper : t ≤ I.upper) :
    x * t ≤
      max (max (|a * I.lower|) (|a * I.upper|))
        (max (|b * I.lower|) (|b * I.upper|)) := by
  exact mul_le_max_corner_abs_of_mem_interval
    a b I.lower I.upper x t hxa hxb ht_lower ht_upper

/-- The complex norm agrees with the complex absolute value. -/
theorem complex_norm_eq_abs
    (w : ℂ) :
    ‖w‖ = Complex.abs w := by
  rfl

/-- The complex exponential absolute value is the exponential of the real part. -/
theorem complexAbs_exp_eq_realExp_re
    (w : ℂ) :
    Complex.abs (Complex.exp w) = Real.exp w.re := by
  exact Complex.abs_exp w

/-- Norm of the complex exponential is the exponential of the real part. -/
theorem complexExp_norm_eq_realExp_re
    (w : ℂ) :
    ‖Complex.exp w‖ = Real.exp w.re := by
  exact Eq.trans
    (complex_norm_eq_abs (Complex.exp w))
    (complexAbs_exp_eq_realExp_re w)

/-- Multiplication by a real scalar has the expected real part. -/
theorem complex_mul_real_re
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).re = z.re * t := by
  calc
    (z * (t : ℂ)).re = z.re * (t : ℂ).re - z.im * (t : ℂ).im := by
      exact Complex.mul_re z (t : ℂ)
    _ = z.re * t - z.im * (t : ℂ).im := by
      exact congrArg (fun v : ℝ => z.re * v - z.im * (t : ℂ).im)
        (Complex.ofReal_re t)
    _ = z.re * t - z.im * 0 := by
      exact congrArg (fun v : ℝ => z.re * t - z.im * v)
        (Complex.ofReal_im t)
    _ = z.re * t - 0 := by
      exact congrArg (fun v : ℝ => z.re * t - v) (mul_zero z.im)
    _ = z.re * t := sub_zero (z.re * t)

/-- Multiplication by a real scalar has the expected imaginary part. -/
theorem complex_mul_real_im
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).im = z.im * t := by
  calc
    (z * (t : ℂ)).im = z.re * (t : ℂ).im + z.im * (t : ℂ).re := by
      exact Complex.mul_im z (t : ℂ)
    _ = z.re * 0 + z.im * (t : ℂ).re := by
      exact congrArg (fun v : ℝ => z.re * v + z.im * (t : ℂ).re)
        (Complex.ofReal_im t)
    _ = z.re * 0 + z.im * t := by
      exact congrArg (fun v : ℝ => z.re * 0 + z.im * v)
        (Complex.ofReal_re t)
    _ = 0 + z.im * t := by
      exact congrArg (fun v : ℝ => v + z.im * t) (mul_zero z.re)
    _ = z.im * t := zero_add (z.im * t)

/-- A real multiple of `I` has zero real part. -/
theorem paley_ofReal_mul_I_re_zero (t : ℝ) :
    ((t : ℂ) * Complex.I).re = 0 :=
  Eq.trans
    (Complex.mul_I_re (t : ℂ))
    (Eq.trans
      (congrArg Neg.neg (Complex.ofReal_im t))
      (neg_zero : -(0 : ℝ) = 0))

/-- A real multiple of `I` has the expected imaginary part. -/
theorem paley_ofReal_mul_I_im (t : ℝ) :
    ((t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.mul_I_im (t : ℂ))
    (Complex.ofReal_re t)

/-- A horizontal real part plus a vertical real multiple of `I` has real part equal to
the horizontal coordinate. -/
theorem paley_ofReal_add_mul_I_re (a t : ℝ) :
    ((a : ℂ) + (t : ℂ) * Complex.I).re = a :=
  Eq.trans
    (Complex.add_re (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd (Complex.ofReal_re a) (paley_ofReal_mul_I_re_zero t))
      (add_zero a))

/-- A horizontal real part plus a vertical real multiple of `I` has imaginary part equal
to the vertical coordinate. -/
theorem paley_ofReal_add_mul_I_im (a t : ℝ) :
    ((a : ℂ) + (t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.add_im (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd (Complex.ofReal_im a) (paley_ofReal_mul_I_im t))
      (zero_add t))

/-- The real part of the explicit vertical-line decomposition is the horizontal part. -/
theorem complex_verticalLine_decomposition_rhs_re
    (z : ℂ) (t : ℝ) :
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).re =
      z.re * t := by
  have hIcomm :
      Complex.I * (z.im : ℂ) * (t : ℂ) =
        ((z.im * t : ℝ) : ℂ) * Complex.I := by
    calc
      Complex.I * (z.im : ℂ) * (t : ℂ) =
          ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
        calc
          Complex.I * (z.im : ℂ) * (t : ℂ) =
              (z.im : ℂ) * Complex.I * (t : ℂ) := by
            exact congrArg (fun v : ℂ => v * (t : ℂ))
              (mul_comm Complex.I (z.im : ℂ))
          _ = (z.im : ℂ) * ((t : ℂ) * Complex.I) := by
            exact Eq.trans
              (mul_assoc (z.im : ℂ) Complex.I (t : ℂ))
              (congrArg (fun v : ℂ => (z.im : ℂ) * v)
                (mul_comm Complex.I (t : ℂ)))
          _ = ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
            exact (mul_assoc (z.im : ℂ) (t : ℂ) Complex.I).symm
      _ = ((z.im * t : ℝ) : ℂ) * Complex.I := by
        exact congrArg (fun v : ℂ => v * Complex.I)
          (Complex.ofReal_mul z.im t).symm
  calc
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).re =
        ((z.re * t : ℂ) + ((z.im * t : ℝ) : ℂ) * Complex.I).re := by
      exact congrArg (fun v : ℂ => ((z.re * t : ℂ) + v).re) hIcomm
    _ = z.re * t := by
      have h_re_mul_cast :
          (((z.re * t : ℝ) : ℂ) = (z.re : ℂ) * (t : ℂ)) :=
        Complex.ofReal_mul z.re t
      exact Eq.subst
        (motive := fun v : ℂ =>
          (v + ((z.im * t : ℝ) : ℂ) * Complex.I).re = z.re * t)
        h_re_mul_cast
        (paley_ofReal_add_mul_I_re (z.re * t) (z.im * t))

/-- The imaginary part of the explicit vertical-line decomposition is the vertical part. -/
theorem complex_verticalLine_decomposition_rhs_im
    (z : ℂ) (t : ℝ) :
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).im =
      z.im * t := by
  have hIcomm :
      Complex.I * (z.im : ℂ) * (t : ℂ) =
        ((z.im * t : ℝ) : ℂ) * Complex.I := by
    calc
      Complex.I * (z.im : ℂ) * (t : ℂ) =
          ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
        calc
          Complex.I * (z.im : ℂ) * (t : ℂ) =
              (z.im : ℂ) * Complex.I * (t : ℂ) := by
            exact congrArg (fun v : ℂ => v * (t : ℂ))
              (mul_comm Complex.I (z.im : ℂ))
          _ = (z.im : ℂ) * ((t : ℂ) * Complex.I) := by
            exact Eq.trans
              (mul_assoc (z.im : ℂ) Complex.I (t : ℂ))
              (congrArg (fun v : ℂ => (z.im : ℂ) * v)
                (mul_comm Complex.I (t : ℂ)))
          _ = ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
            exact (mul_assoc (z.im : ℂ) (t : ℂ) Complex.I).symm
      _ = ((z.im * t : ℝ) : ℂ) * Complex.I := by
        exact congrArg (fun v : ℂ => v * Complex.I)
          (Complex.ofReal_mul z.im t).symm
  calc
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).im =
        ((z.re * t : ℂ) + ((z.im * t : ℝ) : ℂ) * Complex.I).im := by
      exact congrArg (fun v : ℂ => ((z.re * t : ℂ) + v).im) hIcomm
    _ = z.im * t := by
      have h_re_mul_cast :
          (((z.re * t : ℝ) : ℂ) = (z.re : ℂ) * (t : ℂ)) :=
        Complex.ofReal_mul z.re t
      exact Eq.subst
        (motive := fun v : ℂ =>
          (v + ((z.im * t : ℝ) : ℂ) * Complex.I).im = z.im * t)
        h_re_mul_cast
        (paley_ofReal_add_mul_I_im (z.re * t) (z.im * t))

/-- Norm of the complex exponential on a vertical line is the exponential of the real
part of the exponent. -/
theorem zetaPaleyWienerComplexExp_norm_eq_realExp
    (z : ℂ) (t : ℝ) :
    ‖Complex.exp (z * (t : ℂ))‖ =
      Real.exp (z.re * t) := by
  have hnorm :
      ‖Complex.exp (z * (t : ℂ))‖ =
        Real.exp (z * (t : ℂ)).re :=
    complexExp_norm_eq_realExp_re (z * (t : ℂ))
  have hre :
      (z * (t : ℂ)).re = z.re * t :=
    complex_mul_real_re z t
  exact hnorm.trans (congrArg Real.exp hre)

/-- The strip exponential envelope bounds the horizontal exponential on the support
interval. -/
theorem zetaPaleyWienerStripExponential_norm_le_envelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ∀ t : ℝ,
        I.lower ≤ t →
        t ≤ I.upper →
        ‖Complex.exp (z * (t : ℂ))‖ ≤
          zetaPaleyWienerStripExponentialEnvelope I a b := by
  intro z hz t ht_lower ht_upper
  have hnorm :
      ‖Complex.exp (z * (t : ℂ))‖ =
        Real.exp (z.re * t) :=
    zetaPaleyWienerComplexExp_norm_eq_realExp z t
  have hproduct :
      z.re * t ≤
        max (max (|a * I.lower|) (|a * I.upper|))
          (max (|b * I.lower|) (|b * I.upper|)) :=
    zetaPaleyWienerStripProduct_le_endpointEnvelope
      f I a b z.re t hz.1 hz.2 ht_lower ht_upper
  have hexp :
      Real.exp (z.re * t) ≤
        zetaPaleyWienerStripExponentialEnvelope I a b := by
    unfold zetaPaleyWienerStripExponentialEnvelope
    exact Real.exp_le_exp.mpr hproduct
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ zetaPaleyWienerStripExponentialEnvelope I a b)
    hnorm.symm
    hexp

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
