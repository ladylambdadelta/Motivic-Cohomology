import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.StripEnvelope.Owner

/-!
# Damped-family strip Phragmen-Lindelof transport

This owner layer contains the damped-family finite-order strip transport theorems.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- Center of the vertical strip `a ≤ re z ≤ b`. -/
def verticalStripCenter
    (a b : ℝ) : ℝ :=
  (a + b) / 2

/-- Width of the vertical strip `a ≤ re z ≤ b`. -/
def verticalStripWidth
    (a b : ℝ) : ℝ :=
  b - a

/-- Holomorphic cosine kernel used in the strip damping argument.

The affine factor maps the vertical strip to the standard strip
`-π / 2 ≤ re w ≤ π / 2`; the real part of `cos w` is nonnegative in the
interior and controls the damping strength. -/
noncomputable def verticalStripCosineDampingKernel
    (a b : ℝ)
    (z : ℂ) : ℂ :=
  Complex.cos
    (((π : ℝ) : ℂ) *
      (z - ((verticalStripCenter a b : ℝ) : ℂ)) /
        ((verticalStripWidth a b : ℝ) : ℂ))

/-- Subcritical holomorphic cosine barrier on a vertical strip.

Unlike the endpoint kernel with frequency `π / (b - a)`, a frequency
`d < π / (b - a)` has strictly positive real part on both closed vertical
boundary lines. -/
noncomputable def verticalStripSubcriticalCosineBarrierKernel
    (a b d : ℝ)
    (z : ℂ) : ℂ :=
  Complex.cos
    (((d : ℝ) : ℂ) *
      (z - ((verticalStripCenter a b : ℝ) : ℂ)))

/-- The holomorphic strip-damped family attached to `f`.

The parameter `ε` is later sent to `0+` after applying the bounded-boundary
Phragmen-Lindelöf theorem to this family. -/
noncomputable def verticalStripCosineDampedFamily
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (z : ℂ) : ℂ :=
  f z *
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripCosineDampingKernel a b z)

/-- The holomorphic subcritical strip-damped family attached to `f`. -/
noncomputable def verticalStripSubcriticalCosineDampedFamily
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (z : ℂ) : ℂ :=
  f z *
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)

/-- Width-dependent scale for the upper-tail exponential damping.

The denominator bounds the imaginary part of the tilted upper-tail coordinate
on the whole closed vertical strip, so this scale keeps the argument of the
outer exponential in a fixed right half-sector. -/
noncomputable def verticalStripUpperTailDampingScale
    (a b : ℝ) : ℝ :=
  π / (4 * (2 * (|a| + |b| + 2)))

/-- Upper-tail exponential damping base.

For `z = x + i y`, this is `(|a| + |b| + 2) + y - i (x - center)`.
Its real part is positive on the upper tail and its imaginary part is uniformly
bounded on a fixed vertical strip. -/
noncomputable def verticalStripUpperTailDampingBase
    (a b : ℝ)
    (z : ℂ) : ℂ :=
  (((|a| + |b| + 2 : ℝ) : ℂ)) -
    Complex.I * (z - ((verticalStripCenter a b : ℝ) : ℂ))

/-- Upper-tail exponential damping kernel. -/
noncomputable def verticalStripUpperTailDampingKernel
    (a b : ℝ)
    (z : ℂ) : ℂ :=
  Complex.exp
    (((verticalStripUpperTailDampingScale a b : ℝ) : ℂ) *
      verticalStripUpperTailDampingBase a b z)

/-- Upper-tail polynomial normalizing kernel.

This is the holomorphic replacement for the non-holomorphic real finite-order
envelope.  Later estimates choose `N` and the coefficient so that the real part
dominates the prescribed finite-order boundary envelope on the upper half-strip.
-/
noncomputable def verticalStripUpperTailPolynomialNormalizerKernel
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (verticalStripUpperTailDampingBase a b z) ^ N

/-- Holomorphic finite-order normalizing family on the upper half-strip. -/
noncomputable def verticalStripUpperTailPolynomialNormalizedFamily
    (f : ℂ → ℂ)
    (a b C : ℝ)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  f z *
    Complex.exp
      (-((C : ℝ) : ℂ) *
        verticalStripUpperTailPolynomialNormalizerKernel a b N z)

/-- Bounded normalized factor for the upper-tail finite-order strip problem.

The factor `A⁻¹` records the boundary envelope constant, while the holomorphic
polynomial exponential records the finite-order height envelope. -/
noncomputable def verticalStripUpperTailPolynomialBoundedFactor
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ((A⁻¹ : ℝ) : ℂ) *
    verticalStripUpperTailPolynomialNormalizedFamily f a b C N z

/-- Degree-dependent upper-tail polynomial normalizing base.

The extra factor `4 * (N + 1)` in the real shift keeps the argument of this
tilted coordinate uniformly small enough that the `N`-th power stays in the
positive real sector on the closed upper half-strip. -/
noncomputable def verticalStripUpperTailDegreePolynomialBase
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ((4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 : ℝ) : ℂ) -
    Complex.I * (z - ((verticalStripCenter a b : ℝ) : ℂ))

/-- Degree-dependent upper-tail polynomial normalizing kernel. -/
noncomputable def verticalStripUpperTailDegreePolynomialKernel
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (verticalStripUpperTailDegreePolynomialBase a b N z) ^ N

/-- Degree-dependent bounded normalized factor for the upper-tail finite-order
strip problem. -/
noncomputable def verticalStripUpperTailDegreePolynomialBoundedFactor
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ((A⁻¹ : ℝ) : ℂ) *
    (f z *
      Complex.exp
        (-((C : ℝ) : ℂ) *
          verticalStripUpperTailDegreePolynomialKernel a b N z))

/-- Mixed upper-tail bounded normalized factor: the subcritical cosine damping
controls horizontal top edges, while the degree-dependent polynomial
normalizer records the finite-order vertical boundary envelope. -/
noncomputable def verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
    (f : ℂ → ℂ)
    (a b d A C ε : ℝ)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  verticalStripUpperTailDegreePolynomialBoundedFactor
    (verticalStripSubcriticalCosineDampedFamily f a b d ε)
    a b A C N z

/-- Holomorphic upper-tail damped family attached to `f`. -/
noncomputable def verticalStripUpperTailDampedFamily
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (z : ℂ) : ℂ :=
  f z *
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripUpperTailDampingKernel a b z)

/-- Unfolding of the strip cosine damping kernel. -/
theorem verticalStripCosineDampingKernel_eq
    (a b : ℝ)
    (z : ℂ) :
    verticalStripCosineDampingKernel a b z =
      Complex.cos
        (((π : ℝ) : ℂ) *
          (z - ((verticalStripCenter a b : ℝ) : ℂ)) /
            ((verticalStripWidth a b : ℝ) : ℂ)) := by
  rfl

/-- Unfolding of the subcritical strip cosine barrier kernel. -/
theorem verticalStripSubcriticalCosineBarrierKernel_eq
    (a b d : ℝ)
    (z : ℂ) :
    verticalStripSubcriticalCosineBarrierKernel a b d z =
      Complex.cos
        (((d : ℝ) : ℂ) *
          (z - ((verticalStripCenter a b : ℝ) : ℂ))) := by
  rfl

/-- Unfolding of the strip cosine damped family. -/
theorem verticalStripCosineDampedFamily_eq
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (z : ℂ) :
    verticalStripCosineDampedFamily f a b ε z =
      f z *
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripCosineDampingKernel a b z) := by
  rfl

/-- Unfolding of the subcritical strip cosine damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_eq
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (z : ℂ) :
    verticalStripSubcriticalCosineDampedFamily f a b d ε z =
      f z *
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripSubcriticalCosineBarrierKernel a b d z) := by
  rfl

/-- Unfolding of the upper-tail damping base. -/
theorem verticalStripUpperTailDampingBase_eq
    (a b : ℝ)
    (z : ℂ) :
    verticalStripUpperTailDampingBase a b z =
      (((|a| + |b| + 2 : ℝ) : ℂ)) -
        Complex.I * (z - ((verticalStripCenter a b : ℝ) : ℂ)) := by
  rfl

/-- Unfolding of the upper-tail damping kernel. -/
theorem verticalStripUpperTailDampingKernel_eq
    (a b : ℝ)
    (z : ℂ) :
    verticalStripUpperTailDampingKernel a b z =
      Complex.exp
        (((verticalStripUpperTailDampingScale a b : ℝ) : ℂ) *
          verticalStripUpperTailDampingBase a b z) := by
  rfl

/-- Unfolding of the upper-tail polynomial normalizing kernel. -/
theorem verticalStripUpperTailPolynomialNormalizerKernel_eq
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailPolynomialNormalizerKernel a b N z =
      (verticalStripUpperTailDampingBase a b z) ^ N := by
  rfl

/-- Unfolding of the upper-tail polynomial normalized family. -/
theorem verticalStripUpperTailPolynomialNormalizedFamily_eq
    (f : ℂ → ℂ)
    (a b C : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailPolynomialNormalizedFamily f a b C N z =
      f z *
        Complex.exp
          (-((C : ℝ) : ℂ) *
            verticalStripUpperTailPolynomialNormalizerKernel a b N z) := by
  rfl

/-- Unfolding of the upper-tail polynomial bounded normalized factor. -/
theorem verticalStripUpperTailPolynomialBoundedFactor_eq
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailPolynomialBoundedFactor f a b A C N z =
      ((A⁻¹ : ℝ) : ℂ) *
        verticalStripUpperTailPolynomialNormalizedFamily f a b C N z := by
  rfl

/-- Unfolding of the degree-dependent polynomial base. -/
theorem verticalStripUpperTailDegreePolynomialBase_eq
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailDegreePolynomialBase a b N z =
      ((4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 : ℝ) : ℂ) -
        Complex.I * (z - ((verticalStripCenter a b : ℝ) : ℂ)) := by
  rfl

/-- Unfolding of the degree-dependent polynomial kernel. -/
theorem verticalStripUpperTailDegreePolynomialKernel_eq
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailDegreePolynomialKernel a b N z =
      (verticalStripUpperTailDegreePolynomialBase a b N z) ^ N := by
  rfl

/-- Unfolding of the degree-dependent bounded normalized factor. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_eq
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z =
      ((A⁻¹ : ℝ) : ℂ) *
        (f z *
          Complex.exp
            (-((C : ℝ) : ℂ) *
              verticalStripUpperTailDegreePolynomialKernel a b N z)) := by
  rfl

/-- Unfolding of the mixed subcritical-cosine/degree-polynomial bounded
normalized factor. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_eq
    (f : ℂ → ℂ)
    (a b d A C ε : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
        f a b d A C ε N z =
      verticalStripUpperTailDegreePolynomialBoundedFactor
        (verticalStripSubcriticalCosineDampedFamily f a b d ε)
        a b A C N z := by
  rfl

/-- Unfolding of the upper-tail damped family. -/
theorem verticalStripUpperTailDampedFamily_eq
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (z : ℂ) :
    verticalStripUpperTailDampedFamily f a b ε z =
      f z *
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripUpperTailDampingKernel a b z) := by
  rfl

/-- Real part of the upper-tail damping base. -/
theorem verticalStripUpperTailDampingBase_re
    (a b : ℝ)
    (z : ℂ) :
    (verticalStripUpperTailDampingBase a b z).re =
      |a| + |b| + 2 + z.im := by
  let c : ℂ := ((verticalStripCenter a b : ℝ) : ℂ)
  let q : ℂ := z - c
  let K : ℝ := |a| + |b| + 2
  have hq_im : q.im = z.im := by
    calc
      q.im = z.im - c.im := Complex.sub_im z c
      _ = z.im - 0 := by
        exact congrArg (fun u : ℝ => z.im - u)
          (Complex.ofReal_im (verticalStripCenter a b))
      _ = z.im := sub_zero z.im
  have hIq_re : (Complex.I * q).re = -z.im := by
    calc
      (Complex.I * q).re = -q.im := Complex.I_mul_re q
      _ = -z.im := congrArg Neg.neg hq_im
  calc
    (verticalStripUpperTailDampingBase a b z).re =
        ((K : ℂ) - Complex.I * q).re := rfl
    _ = (K : ℂ).re - (Complex.I * q).re :=
      Complex.sub_re (K : ℂ) (Complex.I * q)
    _ = K - (Complex.I * q).re := by
      exact congrArg (fun u : ℝ => u - (Complex.I * q).re)
        (Complex.ofReal_re K)
    _ = K - (-z.im) := by
      exact congrArg (fun u : ℝ => K - u) hIq_re
    _ = K + z.im := sub_neg_eq_add K z.im
    _ = |a| + |b| + 2 + z.im := rfl

/-- Imaginary part of the upper-tail damping base. -/
theorem verticalStripUpperTailDampingBase_im
    (a b : ℝ)
    (z : ℂ) :
    (verticalStripUpperTailDampingBase a b z).im =
      -(z.re - verticalStripCenter a b) := by
  let c : ℂ := ((verticalStripCenter a b : ℝ) : ℂ)
  let q : ℂ := z - c
  have hq_re : q.re = z.re - verticalStripCenter a b := by
    calc
      q.re = z.re - c.re := Complex.sub_re z c
      _ = z.re - verticalStripCenter a b := by
        exact congrArg (fun u : ℝ => z.re - u)
          (Complex.ofReal_re (verticalStripCenter a b))
  have hIq_im : (Complex.I * q).im = z.re - verticalStripCenter a b := by
    calc
      (Complex.I * q).im = q.re := Complex.I_mul_im q
      _ = z.re - verticalStripCenter a b := hq_re
  calc
    (verticalStripUpperTailDampingBase a b z).im =
        (((|a| + |b| + 2 : ℝ) : ℂ) - Complex.I * q).im := rfl
    _ = (((|a| + |b| + 2 : ℝ) : ℂ)).im - (Complex.I * q).im :=
      Complex.sub_im (((|a| + |b| + 2 : ℝ) : ℂ)) (Complex.I * q)
    _ = 0 - (Complex.I * q).im := by
      exact congrArg (fun u : ℝ => u - (Complex.I * q).im)
        (Complex.ofReal_im (|a| + |b| + 2))
    _ = -(Complex.I * q).im := zero_sub (Complex.I * q).im
    _ = -(z.re - verticalStripCenter a b) := congrArg Neg.neg hIq_im

/-- Real part of the degree-dependent upper-tail polynomial base. -/
theorem verticalStripUpperTailDegreePolynomialBase_re
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    (verticalStripUpperTailDegreePolynomialBase a b N z).re =
      4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 + z.im := by
  let c : ℂ := ((verticalStripCenter a b : ℝ) : ℂ)
  let q : ℂ := z - c
  let K : ℝ := 4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1
  have hq_im : q.im = z.im := by
    calc
      q.im = z.im - c.im := Complex.sub_im z c
      _ = z.im - 0 := by
        exact congrArg (fun u : ℝ => z.im - u)
          (Complex.ofReal_im (verticalStripCenter a b))
      _ = z.im := sub_zero z.im
  have hIq_re : (Complex.I * q).re = -z.im := by
    calc
      (Complex.I * q).re = -q.im := Complex.I_mul_re q
      _ = -z.im := congrArg Neg.neg hq_im
  calc
    (verticalStripUpperTailDegreePolynomialBase a b N z).re =
        ((K : ℂ) - Complex.I * q).re := rfl
    _ = (K : ℂ).re - (Complex.I * q).re :=
      Complex.sub_re (K : ℂ) (Complex.I * q)
    _ = K - (Complex.I * q).re := by
      exact congrArg (fun u : ℝ => u - (Complex.I * q).re)
        (Complex.ofReal_re K)
    _ = K - (-z.im) := by
      exact congrArg (fun u : ℝ => K - u) hIq_re
    _ = K + z.im := sub_neg_eq_add K z.im
    _ = 4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 + z.im := rfl

/-- Imaginary part of the degree-dependent upper-tail polynomial base. -/
theorem verticalStripUpperTailDegreePolynomialBase_im
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    (verticalStripUpperTailDegreePolynomialBase a b N z).im =
      -(z.re - verticalStripCenter a b) := by
  let c : ℂ := ((verticalStripCenter a b : ℝ) : ℂ)
  let q : ℂ := z - c
  let K : ℝ := 4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1
  have hq_re : q.re = z.re - verticalStripCenter a b := by
    calc
      q.re = z.re - c.re := Complex.sub_re z c
      _ = z.re - verticalStripCenter a b := by
        exact congrArg (fun u : ℝ => z.re - u)
          (Complex.ofReal_re (verticalStripCenter a b))
  have hIq_im : (Complex.I * q).im = z.re - verticalStripCenter a b := by
    calc
      (Complex.I * q).im = q.re := Complex.I_mul_im q
      _ = z.re - verticalStripCenter a b := hq_re
  calc
    (verticalStripUpperTailDegreePolynomialBase a b N z).im =
        ((K : ℂ) - Complex.I * q).im := rfl
    _ = (K : ℂ).im - (Complex.I * q).im :=
      Complex.sub_im (K : ℂ) (Complex.I * q)
    _ = 0 - (Complex.I * q).im := by
      exact congrArg (fun u : ℝ => u - (Complex.I * q).im)
        (Complex.ofReal_im K)
    _ = -(Complex.I * q).im := zero_sub (Complex.I * q).im
    _ = -(z.re - verticalStripCenter a b) := congrArg Neg.neg hIq_im

/-- The upper-tail damping scale is positive. -/
theorem verticalStripUpperTailDampingScale_pos
    (a b : ℝ) :
    0 < verticalStripUpperTailDampingScale a b := by
  have hden_pos : 0 < 4 * (2 * (|a| + |b| + 2)) := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    have hinner_pos : 0 < |a| + |b| + 2 :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_left hsum_nonneg)
    have hscaled_pos : 0 < 2 * (|a| + |b| + 2) :=
      mul_pos zero_lt_two hinner_pos
    exact mul_pos zero_lt_four hscaled_pos
  exact div_pos Real.pi_pos hden_pos

/-- The real part of the upper-tail damping base is positive on the upper
vertical tail. -/
theorem verticalStripUpperTailDampingBase_re_pos_on_upperTail
    (a b : ℝ)
    {z : ℂ}
    (hz_im : 1 ≤ z.im) :
    0 < (verticalStripUpperTailDampingBase a b z).re := by
  have hsum_nonneg : 0 ≤ |a| + |b| :=
    add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hK_nonneg : 0 ≤ |a| + |b| + 2 :=
    le_trans zero_le_two (le_add_of_nonneg_left hsum_nonneg)
  have hone_pos : 0 < (1 : ℝ) := zero_lt_one
  have hre_lower : 0 < |a| + |b| + 2 + z.im := by
    calc
      0 < 0 + 1 := by
        exact Eq.subst (motive := fun x : ℝ => 0 < x) (zero_add 1).symm hone_pos
      _ ≤ (|a| + |b| + 2) + z.im :=
        add_le_add hK_nonneg hz_im
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 < x)
      (verticalStripUpperTailDampingBase_re a b z).symm
      hre_lower

/-- The real part of the degree-dependent polynomial base is positive on the
upper vertical tail. -/
theorem verticalStripUpperTailDegreePolynomialBase_re_pos_on_upperTail
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hz_im : 1 ≤ z.im) :
    0 < (verticalStripUpperTailDegreePolynomialBase a b N z).re := by
  have hsum_nonneg : 0 ≤ |a| + |b| :=
    add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hinner_nonneg : 0 ≤ |a| + |b| + 2 :=
    le_trans zero_le_two (le_add_of_nonneg_left hsum_nonneg)
  have hN_nonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg (N + 1)
  have hshift_nonneg :
      0 ≤ 4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 :=
    add_nonneg
      (mul_nonneg
        (mul_nonneg (le_of_lt zero_lt_four) hN_nonneg)
        hinner_nonneg)
      zero_le_one
  have hre_lower :
      0 < 4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 + z.im := by
    calc
      0 < 0 + 1 := by
        exact Eq.subst (motive := fun x : ℝ => 0 < x)
          (zero_add 1).symm zero_lt_one
      _ ≤ 4 * ((N + 1 : ℕ) : ℝ) * (|a| + |b| + 2) + 1 + z.im :=
        add_le_add hshift_nonneg hz_im
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 < x)
      (verticalStripUpperTailDegreePolynomialBase_re a b N z).symm
      hre_lower

/-- The strip center has a crude endpoint absolute-value bound. -/
theorem verticalStripCenter_abs_le_abs_sum_plus_two
    (a b : ℝ) :
    |verticalStripCenter a b| ≤ |a| + |b| + 2 := by
  let S : ℝ := |a| + |b|
  have hS_nonneg : 0 ≤ S :=
    add_nonneg (abs_nonneg a) (abs_nonneg b)
  have htwo_pos : 0 < (2 : ℝ) :=
    zero_lt_two
  have htwo_nonneg : 0 ≤ (2 : ℝ) :=
    le_of_lt htwo_pos
  have hhalf_le_self : S / 2 ≤ S := by
    have hhalf_eq : S / 2 = (1 / 2) * S := by
      exact (one_div_mul_eq_div S 2).symm
    have hone_half_le_one : (1 / 2 : ℝ) ≤ 1 := by
      exact (div_le_one htwo_pos).mpr (le_of_eq rfl)
    have hscaled : (1 / 2 : ℝ) * S ≤ 1 * S :=
      mul_le_mul_of_nonneg_right hone_half_le_one hS_nonneg
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ S)
        (mul_one S)
        (Eq.subst
          (motive := fun x : ℝ => x ≤ 1 * S)
          hhalf_eq.symm
          hscaled)
  have habs_add : |a + b| ≤ S :=
    abs_add a b
  have hdiv_le : |a + b| / 2 ≤ S / 2 :=
    div_le_div_of_nonneg_right habs_add htwo_nonneg
  have hcenter_eq :
      |verticalStripCenter a b| = |a + b| / 2 := by
    calc
      |verticalStripCenter a b| = |(a + b) / 2| := rfl
      _ = |a + b| / |(2 : ℝ)| := abs_div (a + b) 2
      _ = |a + b| / 2 := by
        exact congrArg (fun x : ℝ => |a + b| / x)
          (abs_of_pos htwo_pos)
  exact
    le_trans
      (le_of_eq hcenter_eq)
      (le_trans hdiv_le
        (le_trans hhalf_le_self
          (le_add_of_nonneg_right zero_le_two)))

/-- In a closed vertical strip, the real coordinate has a crude endpoint
absolute-value bound. -/
theorem verticalStrip_re_abs_le_abs_sum_plus_two
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    |z.re| ≤ |a| + |b| + 2 := by
  let S : ℝ := |a| + |b|
  have hleft : -(|a| + |b| + 2) ≤ z.re := by
    have hneg_le_a : -(|a| + |b| + 2) ≤ a := by
      have hneg_le_neg_abs_a : -(|a| + |b| + 2) ≤ -|a| := by
        have habs_a_le_sum : |a| ≤ |a| + |b| + 2 :=
          le_add_of_nonneg_right
            (add_nonneg (abs_nonneg b) zero_le_two)
        exact neg_le_neg habs_a_le_sum
      exact le_trans hneg_le_neg_abs_a (neg_abs_le a)
    exact le_trans hneg_le_a hza
  have hright : z.re ≤ |a| + |b| + 2 := by
    have hb_le_abs_b : b ≤ |b| :=
      le_abs_self b
    have habs_b_le_sum : |b| ≤ |a| + |b| + 2 := by
      have habs_b_le_abs_sum : |b| ≤ |a| + |b| :=
        le_add_of_nonneg_left (abs_nonneg a)
      exact le_trans habs_b_le_abs_sum (le_add_of_nonneg_right zero_le_two)
    exact le_trans hzb (le_trans hb_le_abs_b habs_b_le_sum)
  exact abs_le.mpr ⟨hleft, hright⟩

/-- The imaginary part of the tilted upper-tail coordinate is uniformly bounded
on a closed vertical strip. -/
theorem verticalStripUpperTailDampingBase_im_abs_le
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    |(verticalStripUpperTailDampingBase a b z).im| ≤
      2 * (|a| + |b| + 2) := by
  let K : ℝ := |a| + |b| + 2
  have hz_abs : |z.re| ≤ K :=
    verticalStrip_re_abs_le_abs_sum_plus_two a b hza hzb
  have hc_abs : |verticalStripCenter a b| ≤ K :=
    verticalStripCenter_abs_le_abs_sum_plus_two a b
  have hsum : |z.re| + |verticalStripCenter a b| ≤ K + K :=
    add_le_add hz_abs hc_abs
  have hsub : |z.re - verticalStripCenter a b| ≤
      |z.re| + |verticalStripCenter a b| := by
    have hrewrite :
        z.re - verticalStripCenter a b =
          z.re + -(verticalStripCenter a b) := by
      exact sub_eq_add_neg z.re (verticalStripCenter a b)
    have habs_add :
        |z.re + -(verticalStripCenter a b)| ≤
          |z.re| + |-(verticalStripCenter a b)| :=
      abs_add z.re (-(verticalStripCenter a b))
    have hneg_abs :
        |-(verticalStripCenter a b)| = |verticalStripCenter a b| :=
      abs_neg (verticalStripCenter a b)
    exact
      le_trans
        (Eq.subst
          (motive := fun x : ℝ =>
            |x| ≤ |z.re| + |verticalStripCenter a b|)
          hrewrite
          (Eq.subst
            (motive := fun x : ℝ =>
              |z.re + -(verticalStripCenter a b)| ≤ |z.re| + x)
            hneg_abs
            habs_add))
        (le_of_eq rfl)
  have him_eq :
      |(verticalStripUpperTailDampingBase a b z).im| =
        |z.re - verticalStripCenter a b| := by
    calc
      |(verticalStripUpperTailDampingBase a b z).im| =
          |-(z.re - verticalStripCenter a b)| := by
        exact congrArg abs (verticalStripUpperTailDampingBase_im a b z)
      _ = |z.re - verticalStripCenter a b| :=
        abs_neg (z.re - verticalStripCenter a b)
  have hK_add : K + K = 2 * K := by
    calc
      K + K = 1 * K + 1 * K := by
        exact congrArg₂ HAdd.hAdd (one_mul K).symm (one_mul K).symm
      _ = (1 + 1) * K := by
        exact (add_mul 1 1 K).symm
      _ = 2 * K := rfl
  exact
    le_trans
      (le_of_eq him_eq)
      (le_trans hsub
        (le_trans hsum (le_of_eq hK_add)))

/-- The imaginary part of the degree-dependent tilted coordinate is uniformly
bounded on a closed vertical strip. -/
theorem verticalStripUpperTailDegreePolynomialBase_im_abs_le
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
      2 * (|a| + |b| + 2) := by
  let K : ℝ := |a| + |b| + 2
  have hz_abs : |z.re| ≤ K :=
    verticalStrip_re_abs_le_abs_sum_plus_two a b hza hzb
  have hc_abs : |verticalStripCenter a b| ≤ K :=
    verticalStripCenter_abs_le_abs_sum_plus_two a b
  have hsum : |z.re| + |verticalStripCenter a b| ≤ K + K :=
    add_le_add hz_abs hc_abs
  have hsub : |z.re - verticalStripCenter a b| ≤
      |z.re| + |verticalStripCenter a b| := by
    have hrewrite :
        z.re - verticalStripCenter a b =
          z.re + -(verticalStripCenter a b) := by
      exact sub_eq_add_neg z.re (verticalStripCenter a b)
    have habs_add :
        |z.re + -(verticalStripCenter a b)| ≤
          |z.re| + |-(verticalStripCenter a b)| :=
      abs_add z.re (-(verticalStripCenter a b))
    have hneg_abs :
        |-(verticalStripCenter a b)| = |verticalStripCenter a b| :=
      abs_neg (verticalStripCenter a b)
    exact
      le_trans
        (Eq.subst
          (motive := fun x : ℝ =>
            |x| ≤ |z.re| + |verticalStripCenter a b|)
          hrewrite
          (Eq.subst
            (motive := fun x : ℝ =>
              |z.re + -(verticalStripCenter a b)| ≤ |z.re| + x)
            hneg_abs
            habs_add))
        (le_of_eq rfl)
  have him_eq :
      |(verticalStripUpperTailDegreePolynomialBase a b N z).im| =
        |z.re - verticalStripCenter a b| := by
    calc
      |(verticalStripUpperTailDegreePolynomialBase a b N z).im| =
          |-(z.re - verticalStripCenter a b)| := by
        exact congrArg abs
          (verticalStripUpperTailDegreePolynomialBase_im a b N z)
      _ = |z.re - verticalStripCenter a b| :=
        abs_neg (z.re - verticalStripCenter a b)
  have hK_add : K + K = 2 * K := by
    calc
      K + K = 1 * K + 1 * K := by
        exact congrArg₂ HAdd.hAdd (one_mul K).symm (one_mul K).symm
      _ = (1 + 1) * K := by
        exact (add_mul 1 1 K).symm
      _ = 2 * K := rfl
  exact
    le_trans
      (le_of_eq him_eq)
      (le_trans hsub
        (le_trans hsum (le_of_eq hK_add)))

/-- On the closed upper tail, the degree-dependent shift makes the imaginary
part of the tilted coordinate small compared with its real part. -/
theorem verticalStripUpperTailDegreePolynomialBase_degree_mul_im_abs_le_re
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im) :
    ((N + 1 : ℕ) : ℝ) *
        |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
      (verticalStripUpperTailDegreePolynomialBase a b N z).re := by
  let M : ℝ := ((N + 1 : ℕ) : ℝ)
  let K : ℝ := |a| + |b| + 2
  have hM_nonneg : 0 ≤ M :=
    Nat.cast_nonneg (N + 1)
  have hK_nonneg : 0 ≤ K := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    exact le_trans zero_le_two (le_add_of_nonneg_left hsum_nonneg)
  have him :
      |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
        2 * K :=
    verticalStripUpperTailDegreePolynomialBase_im_abs_le a b N hza hzb
  have hleft_le : M *
      |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
        M * (2 * K) :=
    mul_le_mul_of_nonneg_left him hM_nonneg
  have hMK_nonneg : 0 ≤ M * K :=
    mul_nonneg hM_nonneg hK_nonneg
  have htwo_le_four :
      M * (2 * K) ≤ 4 * M * K := by
    have hleft_eq : M * (2 * K) = 2 * (M * K) := by
      calc
        M * (2 * K) = (M * 2) * K := (mul_assoc M 2 K).symm
        _ = (2 * M) * K := congrArg (fun x : ℝ => x * K) (mul_comm M 2)
        _ = 2 * (M * K) := mul_assoc 2 M K
    have hright_eq : 4 * M * K = 4 * (M * K) :=
      mul_assoc 4 M K
    have hscale :
        2 * (M * K) ≤ 4 * (M * K) :=
      mul_le_mul_of_nonneg_right
        (show (2 : ℝ) ≤ 4 from by
          calc
            (2 : ℝ) ≤ 2 + 2 := le_add_of_nonneg_right zero_le_two
            _ = 4 := two_add_two_eq_four)
        hMK_nonneg
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 4 * M * K)
        hleft_eq.symm
        (Eq.subst
          (motive := fun x : ℝ => 2 * (M * K) ≤ x)
          hright_eq.symm
          hscale)
  have hre_lower :
      4 * M * K ≤
        4 * M * K + 1 + z.im := by
    have hone_im_nonneg : 0 ≤ 1 + z.im :=
      add_nonneg zero_le_one (le_trans zero_le_one hz_im)
    calc
      4 * M * K ≤ 4 * M * K + (1 + z.im) :=
        le_add_of_nonneg_right hone_im_nonneg
      _ = 4 * M * K + 1 + z.im := (add_assoc (4 * M * K) 1 z.im).symm
  have hre_eq :
      (verticalStripUpperTailDegreePolynomialBase a b N z).re =
        4 * M * K + 1 + z.im :=
    verticalStripUpperTailDegreePolynomialBase_re a b N z
  exact
    le_trans hleft_le
      (le_trans htwo_le_four
        (Eq.subst
          (motive := fun x : ℝ => 4 * M * K ≤ x)
          hre_eq.symm
          hre_lower))

/-- On the closed upper tail, the degree-dependent shift actually gives a
factor-two sector margin.  This strengthened form is the scalar input for the
real-part lower bound of the degree-dependent polynomial normalizer. -/
theorem verticalStripUpperTailDegreePolynomialBase_two_degree_mul_im_abs_le_re
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im) :
    2 * ((N + 1 : ℕ) : ℝ) *
        |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
      (verticalStripUpperTailDegreePolynomialBase a b N z).re := by
  let M : ℝ := ((N + 1 : ℕ) : ℝ)
  let K : ℝ := |a| + |b| + 2
  have hM_nonneg : 0 ≤ M :=
    Nat.cast_nonneg (N + 1)
  have hK_nonneg : 0 ≤ K := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    exact le_trans zero_le_two (le_add_of_nonneg_left hsum_nonneg)
  have him :
      |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
        2 * K :=
    verticalStripUpperTailDegreePolynomialBase_im_abs_le a b N hza hzb
  have hleft_le :
      2 * M *
          |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
        2 * M * (2 * K) :=
    mul_le_mul_of_nonneg_left him
      (mul_nonneg zero_le_two hM_nonneg)
  have hMK_nonneg : 0 ≤ M * K :=
    mul_nonneg hM_nonneg hK_nonneg
  have htwo_two_le_four :
      2 * M * (2 * K) ≤ 4 * M * K := by
    have hleft_eq : 2 * M * (2 * K) = 4 * (M * K) := by
      calc
        2 * M * (2 * K) = (2 * M) * (2 * K) := rfl
        _ = ((2 * M) * 2) * K := (mul_assoc (2 * M) 2 K).symm
        _ = (2 * (M * 2)) * K := by
          exact congrArg (fun x : ℝ => x * K) (mul_assoc 2 M 2)
        _ = (2 * (2 * M)) * K := by
          exact congrArg (fun x : ℝ => (2 * x) * K) (mul_comm M 2)
        _ = ((2 * 2) * M) * K := by
          exact congrArg (fun x : ℝ => x * K) (mul_assoc 2 2 M).symm
        _ = (4 * M) * K := rfl
        _ = 4 * (M * K) := mul_assoc 4 M K
    have hright_eq : 4 * M * K = 4 * (M * K) :=
      mul_assoc 4 M K
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 4 * M * K)
        hleft_eq.symm
        (Eq.subst
          (motive := fun x : ℝ => 4 * (M * K) ≤ x)
          hright_eq.symm
          (le_of_eq rfl))
  have hre_lower :
      4 * M * K ≤
        4 * M * K + 1 + z.im := by
    have hone_im_nonneg : 0 ≤ 1 + z.im :=
      add_nonneg zero_le_one (le_trans zero_le_one hz_im)
    calc
      4 * M * K ≤ 4 * M * K + (1 + z.im) :=
        le_add_of_nonneg_right hone_im_nonneg
      _ = 4 * M * K + 1 + z.im := (add_assoc (4 * M * K) 1 z.im).symm
  have hre_eq :
      (verticalStripUpperTailDegreePolynomialBase a b N z).re =
        4 * M * K + 1 + z.im :=
    verticalStripUpperTailDegreePolynomialBase_re a b N z
  exact
    le_trans hleft_le
      (le_trans htwo_two_le_four
        (Eq.subst
          (motive := fun x : ℝ => 4 * M * K ≤ x)
          hre_eq.symm
          hre_lower))

/-- Normalized sector-width form of the degree-dependent base margin. -/
theorem verticalStripUpperTailDegreePolynomialBase_im_abs_le_inv_two_degree_mul_re
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im) :
    |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
      (2 * ((N + 1 : ℕ) : ℝ))⁻¹ *
        (verticalStripUpperTailDegreePolynomialBase a b N z).re := by
  let K : ℝ := 2 * ((N + 1 : ℕ) : ℝ)
  let W : ℂ := verticalStripUpperTailDegreePolynomialBase a b N z
  have hK_pos : 0 < K := by
    have hsucc_pos_nat : 0 < N + 1 :=
      Nat.succ_pos N
    have hsucc_pos_real : 0 < ((N + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr hsucc_pos_nat
    exact mul_pos zero_lt_two hsucc_pos_real
  have hK_inv_nonneg : 0 ≤ K⁻¹ :=
    inv_nonneg.mpr (le_of_lt hK_pos)
  have hmargin :
      K * |W.im| ≤ W.re :=
    verticalStripUpperTailDegreePolynomialBase_two_degree_mul_im_abs_le_re
      a b N hza hzb hz_im
  have hscaled :
      K⁻¹ * (K * |W.im|) ≤ K⁻¹ * W.re :=
    mul_le_mul_of_nonneg_left hmargin hK_inv_nonneg
  have hleft :
      K⁻¹ * (K * |W.im|) = |W.im| := by
    calc
      K⁻¹ * (K * |W.im|) = (K⁻¹ * K) * |W.im| :=
        (mul_assoc K⁻¹ K |W.im|).symm
      _ = 1 * |W.im| :=
        congrArg (fun T : ℝ => T * |W.im|) (inv_mul_cancel₀ hK_pos.ne')
      _ = |W.im| := one_mul |W.im|
  exact
    Eq.subst
      (motive := fun T : ℝ => T ≤ K⁻¹ * W.re)
      hleft
      hscaled

/-- The real part of the degree-dependent polynomial kernel is bounded above by
the corresponding absolute-value power of its base.  This is the elementary
upper-envelope side used when undamping the normalized upper-tail factor. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_le_base_abs_pow
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
      Complex.abs (verticalStripUpperTailDegreePolynomialBase a b N z) ^ N := by
  let W : ℂ := verticalStripUpperTailDegreePolynomialBase a b N z
  have hkernel_eq :
      verticalStripUpperTailDegreePolynomialKernel a b N z = W ^ N :=
    verticalStripUpperTailDegreePolynomialKernel_eq a b N z
  have hre_le_abs : (W ^ N).re ≤ Complex.abs (W ^ N) :=
    Complex.re_le_abs (W ^ N)
  have habs_pow : Complex.abs (W ^ N) = Complex.abs W ^ N :=
    Complex.abs_pow W N
  exact
    Eq.subst
      (motive := fun T : ℝ =>
        (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤ T)
      habs_pow
      (Eq.subst
        (motive := fun T : ℂ => T.re ≤ Complex.abs (W ^ N))
        hkernel_eq.symm
        hre_le_abs)

/-- Norm version of the upper-envelope side for the degree-dependent polynomial
kernel. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_le_base_norm_pow
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
      ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ^ N := by
  let W : ℂ := verticalStripUpperTailDegreePolynomialBase a b N z
  have h_abs :
      Complex.abs W ^ N = ‖W‖ ^ N := by
    exact congrArg (fun x : ℝ => x ^ N) (Complex.norm_eq_abs W).symm
  exact
    Eq.subst
      (motive := fun T : ℝ =>
        (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤ T)
      h_abs
      (verticalStripUpperTailDegreePolynomialKernel_re_le_base_abs_pow a b N z)

/-- The real part of the degree-dependent tilted coordinate dominates the
upper-tail height coordinate. -/
theorem verticalStripUpperTailDegreePolynomialBase_one_add_im_le_re
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hz_im : 1 ≤ z.im) :
    1 + z.im ≤
      (verticalStripUpperTailDegreePolynomialBase a b N z).re := by
  let M : ℝ := ((N + 1 : ℕ) : ℝ)
  let K : ℝ := |a| + |b| + 2
  have hM_nonneg : 0 ≤ M :=
    Nat.cast_nonneg (N + 1)
  have hK_nonneg : 0 ≤ K := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    exact le_trans zero_le_two (le_add_of_nonneg_left hsum_nonneg)
  have hshift_nonneg : 0 ≤ 4 * M * K :=
    mul_nonneg
      (mul_nonneg (le_of_lt zero_lt_four) hM_nonneg)
      hK_nonneg
  have hraw :
      1 + z.im ≤ 4 * M * K + 1 + z.im := by
    calc
      1 + z.im = 0 + (1 + z.im) := (zero_add (1 + z.im)).symm
      _ ≤ 4 * M * K + (1 + z.im) :=
        add_le_add_right hshift_nonneg (1 + z.im)
      _ = 4 * M * K + 1 + z.im :=
        (add_assoc (4 * M * K) 1 z.im).symm
  have hre_eq :
      (verticalStripUpperTailDegreePolynomialBase a b N z).re =
        4 * M * K + 1 + z.im :=
    verticalStripUpperTailDegreePolynomialBase_re a b N z
  exact
    Eq.subst
      (motive := fun T : ℝ => 1 + z.im ≤ T)
      hre_eq.symm
      hraw

/-- Upper-tail height in absolute-value form is dominated by the real part of
the degree-dependent tilted coordinate. -/
theorem verticalStripUpperTailDegreePolynomialBase_one_add_im_norm_le_re
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hz_im : 1 ≤ z.im) :
    1 + ‖z.im‖ ≤
      (verticalStripUpperTailDegreePolynomialBase a b N z).re := by
  have hzim_nonneg : 0 ≤ z.im :=
    le_trans zero_le_one hz_im
  have hnorm_eq : ‖z.im‖ = z.im :=
    Real.norm_of_nonneg hzim_nonneg
  exact
    Eq.subst
      (motive := fun T : ℝ =>
        1 + T ≤ (verticalStripUpperTailDegreePolynomialBase a b N z).re)
      hnorm_eq.symm
      (verticalStripUpperTailDegreePolynomialBase_one_add_im_le_re
        a b N hz_im)

/-- The real part of the degree-dependent tilted coordinate also dominates
each upper-tail height power. -/
theorem verticalStripUpperTailDegreePolynomialBase_one_add_im_norm_pow_le_re_pow
    (a b : ℝ)
    (N p : ℕ)
    {z : ℂ}
    (hz_im : 1 ≤ z.im) :
    (1 + ‖z.im‖) ^ p ≤
      (verticalStripUpperTailDegreePolynomialBase a b N z).re ^ p := by
  have hbase :
      1 + ‖z.im‖ ≤
        (verticalStripUpperTailDegreePolynomialBase a b N z).re :=
    verticalStripUpperTailDegreePolynomialBase_one_add_im_norm_le_re
      a b N hz_im
  have hleft_nonneg : 0 ≤ 1 + ‖z.im‖ :=
    add_nonneg zero_le_one (norm_nonneg z.im)
  exact pow_le_pow_left₀ hleft_nonneg hbase p

/-- Real part of the square of a complex number, expanded in coordinates. -/
theorem complex_sq_re_eq_re_sq_sub_im_sq
    (w : ℂ) :
    (w ^ (2 : ℕ)).re = w.re * w.re - w.im * w.im := by
  have hpow : w ^ (2 : ℕ) = w * w :=
    pow_two w
  have hmul : (w * w).re = w.re * w.re - w.im * w.im :=
    Complex.mul_re w w
  exact
    Eq.trans
      (congrArg Complex.re hpow)
      hmul

/-- A right-sector margin makes the square have nonnegative real part. -/
theorem complex_sq_re_nonneg_of_im_abs_le_re
    {w : ℂ}
    (hre_nonneg : 0 ≤ w.re)
    (him_le : |w.im| ≤ w.re) :
    0 ≤ (w ^ (2 : ℕ)).re := by
  have him_nonneg : 0 ≤ |w.im| :=
    abs_nonneg w.im
  have him_sq_le_re_sq :
      |w.im| * |w.im| ≤ w.re * w.re :=
    mul_le_mul him_le him_le him_nonneg hre_nonneg
  have him_sq_eq_abs_sq :
      w.im * w.im = |w.im| * |w.im| := by
    have hsq : |w.im| ^ (2 : ℕ) = w.im ^ (2 : ℕ) :=
      sq_abs w.im
    calc
      w.im * w.im = w.im ^ (2 : ℕ) := (pow_two w.im).symm
      _ = |w.im| ^ (2 : ℕ) := hsq.symm
      _ = |w.im| * |w.im| := pow_two |w.im|
  have hsub_nonneg :
      0 ≤ w.re * w.re - w.im * w.im := by
    have hrewritten :
        w.im * w.im ≤ w.re * w.re :=
      Eq.subst
        (motive := fun T : ℝ => T ≤ w.re * w.re)
        him_sq_eq_abs_sq.symm
        him_sq_le_re_sq
    exact sub_nonneg.mpr hrewritten
  exact
    Eq.subst
      (motive := fun T : ℝ => 0 ≤ T)
      (complex_sq_re_eq_re_sq_sub_im_sq w).symm
      hsub_nonneg

/-- The degree-dependent tilted coordinate has square with nonnegative real
part on the closed upper half-strip. -/
theorem verticalStripUpperTailDegreePolynomialBase_sq_re_nonneg_on_upperTail
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im) :
    0 ≤
      ((verticalStripUpperTailDegreePolynomialBase a b (2 : ℕ) z) ^
        (2 : ℕ)).re := by
  let W : ℂ := verticalStripUpperTailDegreePolynomialBase a b (2 : ℕ) z
  have hre_pos : 0 < W.re :=
    verticalStripUpperTailDegreePolynomialBase_re_pos_on_upperTail
      a b (2 : ℕ) hz_im
  have hsector :
      2 * (((2 : ℕ) + 1 : ℕ) : ℝ) * |W.im| ≤ W.re :=
    verticalStripUpperTailDegreePolynomialBase_two_degree_mul_im_abs_le_re
      a b (2 : ℕ) hza hzb hz_im
  have him_le_scaled :
      |W.im| ≤ 2 * (((2 : ℕ) + 1 : ℕ) : ℝ) * |W.im| := by
    have hone_le_factor :
        (1 : ℝ) ≤ 2 * (((2 : ℕ) + 1 : ℕ) : ℝ) := by
      have hfactor_eq :
          2 * (((2 : ℕ) + 1 : ℕ) : ℝ) = 6 := rfl
      have hone_le_six : (1 : ℝ) ≤ 6 := by
        calc
          (1 : ℝ) ≤ 2 := one_le_two
          _ ≤ 2 + 4 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 4 from zero_le_four)
          _ = 6 := by
            rfl
      exact
        Eq.subst
          (motive := fun T : ℝ => (1 : ℝ) ≤ T)
          hfactor_eq.symm
          hone_le_six
    have him_nonneg : 0 ≤ |W.im| :=
      abs_nonneg W.im
    calc
      |W.im| = 1 * |W.im| := (one_mul |W.im|).symm
      _ ≤ 2 * (((2 : ℕ) + 1 : ℕ) : ℝ) * |W.im| :=
        mul_le_mul_of_nonneg_right hone_le_factor him_nonneg
  have him_le_re : |W.im| ≤ W.re :=
    le_trans him_le_scaled hsector
  exact
    complex_sq_re_nonneg_of_im_abs_le_re
      (le_of_lt hre_pos)
      him_le_re

/-- Quantitative real-part lower bound for multiplying two complex numbers in
right sectors.  This is the local multiplicative step used in the arbitrary
degree sector-power estimate for the degree-dependent polynomial normalizer. -/
theorem complex_mul_re_ge_half_re_mul_re_of_sector_bounds
    {u v : ℂ}
    {A B : ℝ}
    (hu_re_nonneg : 0 ≤ u.re)
    (hv_re_nonneg : 0 ≤ v.re)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hu_im : |u.im| ≤ A * u.re)
    (hv_im : |v.im| ≤ B * v.re)
    (hAB : A * B ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) * (u.re * v.re) ≤ (u * v).re := by
  have hu_scale_nonneg : 0 ≤ A * u.re :=
    mul_nonneg hA_nonneg hu_re_nonneg
  have hv_scale_nonneg : 0 ≤ B * v.re :=
    mul_nonneg hB_nonneg hv_re_nonneg
  have him_abs_mul :
      |u.im * v.im| ≤ (A * u.re) * (B * v.re) := by
    have hmul_abs :
        |u.im * v.im| = |u.im| * |v.im| :=
      abs_mul u.im v.im
    have hscaled :
        |u.im| * |v.im| ≤ (A * u.re) * (B * v.re) :=
      mul_le_mul hu_im hv_im (abs_nonneg v.im) hu_scale_nonneg
    exact
      Eq.subst
        (motive := fun T : ℝ => T ≤ (A * u.re) * (B * v.re))
        hmul_abs.symm
        hscaled
  have hscaled_eq :
      (A * u.re) * (B * v.re) =
        (A * B) * (u.re * v.re) := by
    calc
      (A * u.re) * (B * v.re) =
          ((A * u.re) * B) * v.re := (mul_assoc (A * u.re) B v.re).symm
      _ = (A * (u.re * B)) * v.re := by
        exact congrArg (fun T : ℝ => T * v.re) (mul_assoc A u.re B)
      _ = (A * (B * u.re)) * v.re := by
        exact congrArg (fun T : ℝ => (A * T) * v.re) (mul_comm u.re B)
      _ = ((A * B) * u.re) * v.re := by
        exact congrArg (fun T : ℝ => T * v.re) (mul_assoc A B u.re).symm
      _ = (A * B) * (u.re * v.re) := mul_assoc (A * B) u.re v.re
  have hre_mul_nonneg : 0 ≤ u.re * v.re :=
    mul_nonneg hu_re_nonneg hv_re_nonneg
  have hscaled_le_half :
      (A * u.re) * (B * v.re) ≤
        (1 / 2 : ℝ) * (u.re * v.re) :=
    Eq.subst
      (motive := fun T : ℝ => T ≤ (1 / 2 : ℝ) * (u.re * v.re))
      hscaled_eq.symm
      (mul_le_mul_of_nonneg_right hAB hre_mul_nonneg)
  have him_abs_le_half :
      |u.im * v.im| ≤ (1 / 2 : ℝ) * (u.re * v.re) :=
    le_trans him_abs_mul hscaled_le_half
  have hneg_half_le :
      -((1 / 2 : ℝ) * (u.re * v.re)) ≤ -(u.im * v.im) := by
    have hprod_le_abs : u.im * v.im ≤ |u.im * v.im| :=
      le_abs_self (u.im * v.im)
    have hprod_le_half :
        u.im * v.im ≤ (1 / 2 : ℝ) * (u.re * v.re) :=
      le_trans hprod_le_abs him_abs_le_half
    exact neg_le_neg hprod_le_half
  have hre_eq :
      (u * v).re = u.re * v.re - u.im * v.im :=
    Complex.mul_re u v
  have htarget_raw :
      (1 / 2 : ℝ) * (u.re * v.re) ≤
        u.re * v.re - u.im * v.im := by
    have hhalf_add_half :
        (1 / 2 : ℝ) * (u.re * v.re) +
            (1 / 2 : ℝ) * (u.re * v.re) =
          u.re * v.re := by
      calc
        (1 / 2 : ℝ) * (u.re * v.re) +
            (1 / 2 : ℝ) * (u.re * v.re) =
            ((1 / 2 : ℝ) + (1 / 2 : ℝ)) * (u.re * v.re) :=
          (add_mul (1 / 2 : ℝ) (1 / 2 : ℝ) (u.re * v.re)).symm
        _ = 1 * (u.re * v.re) := by
          exact congrArg (fun T : ℝ => T * (u.re * v.re))
            (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by
              exact add_halves 1)
        _ = u.re * v.re := one_mul (u.re * v.re)
    calc
      (1 / 2 : ℝ) * (u.re * v.re) =
          u.re * v.re + -((1 / 2 : ℝ) * (u.re * v.re)) := by
        have hsum :
            u.re * v.re + -((1 / 2 : ℝ) * (u.re * v.re)) =
              (1 / 2 : ℝ) * (u.re * v.re) := by
          calc
            u.re * v.re + -((1 / 2 : ℝ) * (u.re * v.re)) =
                ((1 / 2 : ℝ) * (u.re * v.re) +
                    (1 / 2 : ℝ) * (u.re * v.re)) +
                  -((1 / 2 : ℝ) * (u.re * v.re)) := by
              exact congrArg
                (fun T : ℝ => T + -((1 / 2 : ℝ) * (u.re * v.re)))
                hhalf_add_half.symm
            _ =
                (1 / 2 : ℝ) * (u.re * v.re) +
                  ((1 / 2 : ℝ) * (u.re * v.re) +
                    -((1 / 2 : ℝ) * (u.re * v.re))) :=
              add_assoc
                ((1 / 2 : ℝ) * (u.re * v.re))
                ((1 / 2 : ℝ) * (u.re * v.re))
                (-((1 / 2 : ℝ) * (u.re * v.re)))
            _ = (1 / 2 : ℝ) * (u.re * v.re) + 0 := by
              exact congrArg
                (fun T : ℝ => (1 / 2 : ℝ) * (u.re * v.re) + T)
                (add_neg_cancel ((1 / 2 : ℝ) * (u.re * v.re)))
            _ = (1 / 2 : ℝ) * (u.re * v.re) :=
              add_zero ((1 / 2 : ℝ) * (u.re * v.re))
        exact hsum.symm
      _ ≤ u.re * v.re + -(u.im * v.im) :=
        add_le_add_left hneg_half_le (u.re * v.re)
      _ = u.re * v.re - u.im * v.im :=
        (sub_eq_add_neg (u.re * v.re) (u.im * v.im)).symm
  exact
    Eq.subst
      (motive := fun T : ℝ => (1 / 2 : ℝ) * (u.re * v.re) ≤ T)
      hre_eq.symm
      htarget_raw

/-- Imaginary-part sector width under multiplication.  If two factors have
nonnegative real part and imaginary part bounded by scalar multiples of their
real parts, then the product has imaginary part bounded by the sum of the two
sector widths times the product of the real parts. -/
theorem complex_mul_im_abs_le_sum_sector_widths
    {u v : ℂ}
    {A B : ℝ}
    (hu_re_nonneg : 0 ≤ u.re)
    (hv_re_nonneg : 0 ≤ v.re)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hu_im : |u.im| ≤ A * u.re)
    (hv_im : |v.im| ≤ B * v.re) :
    |(u * v).im| ≤ (A + B) * (u.re * v.re) := by
  have him_eq :
      (u * v).im = u.re * v.im + u.im * v.re :=
    Complex.mul_im u v
  have hterm_left :
      |u.re * v.im| ≤ B * (u.re * v.re) := by
    have habs_mul :
        |u.re * v.im| = |u.re| * |v.im| :=
      abs_mul u.re v.im
    have hre_abs : |u.re| = u.re :=
      abs_of_nonneg hu_re_nonneg
    have hraw :
        |u.re| * |v.im| ≤ u.re * (B * v.re) := by
      have hleft_nonneg : 0 ≤ |u.re| :=
        abs_nonneg u.re
      exact
        Eq.subst
          (motive := fun T : ℝ => |u.re| * |v.im| ≤ T * (B * v.re))
          hre_abs.symm
          (mul_le_mul_of_nonneg_left hv_im hleft_nonneg)
    have htarget :
        u.re * (B * v.re) = B * (u.re * v.re) := by
      calc
        u.re * (B * v.re) = (u.re * B) * v.re := (mul_assoc u.re B v.re).symm
        _ = (B * u.re) * v.re := congrArg (fun T : ℝ => T * v.re) (mul_comm u.re B)
        _ = B * (u.re * v.re) := mul_assoc B u.re v.re
    exact
      Eq.subst
        (motive := fun T : ℝ => |u.re * v.im| ≤ T)
        htarget
        (Eq.subst
          (motive := fun T : ℝ => T ≤ u.re * (B * v.re))
          habs_mul.symm
          hraw)
  have hterm_right :
      |u.im * v.re| ≤ A * (u.re * v.re) := by
    have habs_mul :
        |u.im * v.re| = |u.im| * |v.re| :=
      abs_mul u.im v.re
    have hre_abs : |v.re| = v.re :=
      abs_of_nonneg hv_re_nonneg
    have hraw :
        |u.im| * |v.re| ≤ (A * u.re) * v.re := by
      have hright_nonneg : 0 ≤ |v.re| :=
        abs_nonneg v.re
      exact
        Eq.subst
          (motive := fun T : ℝ => |u.im| * |v.re| ≤ (A * u.re) * T)
          hre_abs.symm
          (mul_le_mul_of_nonneg_right hu_im hright_nonneg)
    have htarget :
        (A * u.re) * v.re = A * (u.re * v.re) :=
      mul_assoc A u.re v.re
    exact
      Eq.subst
        (motive := fun T : ℝ => |u.im * v.re| ≤ T)
        htarget
        (Eq.subst
          (motive := fun T : ℝ => T ≤ (A * u.re) * v.re)
          habs_mul.symm
          hraw)
  have habs_sum :
      |u.re * v.im + u.im * v.re| ≤
        |u.re * v.im| + |u.im * v.re| :=
    abs_add (u.re * v.im) (u.im * v.re)
  have hsum_terms :
      |u.re * v.im| + |u.im * v.re| ≤
        B * (u.re * v.re) + A * (u.re * v.re) :=
    add_le_add hterm_left hterm_right
  have hsum_eq :
      B * (u.re * v.re) + A * (u.re * v.re) =
        (A + B) * (u.re * v.re) := by
    calc
      B * (u.re * v.re) + A * (u.re * v.re) =
          A * (u.re * v.re) + B * (u.re * v.re) :=
        add_comm (B * (u.re * v.re)) (A * (u.re * v.re))
      _ = (A + B) * (u.re * v.re) :=
        (add_mul A B (u.re * v.re)).symm
  exact
    Eq.subst
      (motive := fun T : ℝ => |(u * v).im| ≤ T)
      hsum_eq
      (Eq.subst
        (motive := fun T : ℝ => |T| ≤ B * (u.re * v.re) + A * (u.re * v.re))
        him_eq.symm
        (le_trans habs_sum hsum_terms))

/-- Exact real-part lower bound for multiplying two factors in right sectors. -/
theorem complex_mul_re_ge_one_sub_mul_sector_widths
    {u v : ℂ}
    {A B : ℝ}
    (hu_re_nonneg : 0 ≤ u.re)
    (hv_re_nonneg : 0 ≤ v.re)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hu_im : |u.im| ≤ A * u.re)
    (hv_im : |v.im| ≤ B * v.re) :
    (1 - A * B) * (u.re * v.re) ≤ (u * v).re := by
  have hu_scale_nonneg : 0 ≤ A * u.re :=
    mul_nonneg hA_nonneg hu_re_nonneg
  have him_abs_mul :
      |u.im * v.im| ≤ (A * u.re) * (B * v.re) := by
    have hmul_abs :
        |u.im * v.im| = |u.im| * |v.im| :=
      abs_mul u.im v.im
    have hscaled :
        |u.im| * |v.im| ≤ (A * u.re) * (B * v.re) :=
      mul_le_mul hu_im hv_im (abs_nonneg v.im) hu_scale_nonneg
    exact
      Eq.subst
        (motive := fun T : ℝ => T ≤ (A * u.re) * (B * v.re))
        hmul_abs.symm
        hscaled
  have hscaled_eq :
      (A * u.re) * (B * v.re) =
        (A * B) * (u.re * v.re) := by
    calc
      (A * u.re) * (B * v.re) =
          ((A * u.re) * B) * v.re := (mul_assoc (A * u.re) B v.re).symm
      _ = (A * (u.re * B)) * v.re :=
        congrArg (fun T : ℝ => T * v.re) (mul_assoc A u.re B)
      _ = (A * (B * u.re)) * v.re :=
        congrArg (fun T : ℝ => (A * T) * v.re) (mul_comm u.re B)
      _ = ((A * B) * u.re) * v.re :=
        congrArg (fun T : ℝ => T * v.re) (mul_assoc A B u.re).symm
      _ = (A * B) * (u.re * v.re) := mul_assoc (A * B) u.re v.re
  have him_abs_bound :
      |u.im * v.im| ≤ (A * B) * (u.re * v.re) :=
    Eq.subst
      (motive := fun T : ℝ => |u.im * v.im| ≤ T)
      hscaled_eq
      him_abs_mul
  have hneg_bound :
      -((A * B) * (u.re * v.re)) ≤ -(u.im * v.im) := by
    have hprod_le_abs : u.im * v.im ≤ |u.im * v.im| :=
      le_abs_self (u.im * v.im)
    have hprod_le_bound :
        u.im * v.im ≤ (A * B) * (u.re * v.re) :=
      le_trans hprod_le_abs him_abs_bound
    exact neg_le_neg hprod_le_bound
  have hre_eq :
      (u * v).re = u.re * v.re - u.im * v.im :=
    Complex.mul_re u v
  have hraw :
      (1 - A * B) * (u.re * v.re) ≤
        u.re * v.re - u.im * v.im := by
    have hleft_eq :
        (1 - A * B) * (u.re * v.re) =
          u.re * v.re + -((A * B) * (u.re * v.re)) := by
      calc
        (1 - A * B) * (u.re * v.re) =
            1 * (u.re * v.re) - (A * B) * (u.re * v.re) :=
          sub_mul 1 (A * B) (u.re * v.re)
        _ = u.re * v.re - (A * B) * (u.re * v.re) :=
          congrArg
            (fun T : ℝ => T - (A * B) * (u.re * v.re))
            (one_mul (u.re * v.re))
        _ = u.re * v.re + -((A * B) * (u.re * v.re)) :=
          sub_eq_add_neg (u.re * v.re) ((A * B) * (u.re * v.re))
    calc
      (1 - A * B) * (u.re * v.re) =
          u.re * v.re + -((A * B) * (u.re * v.re)) := hleft_eq
      _ ≤ u.re * v.re + -(u.im * v.im) :=
        add_le_add_left hneg_bound (u.re * v.re)
      _ = u.re * v.re - u.im * v.im :=
        (sub_eq_add_neg (u.re * v.re) (u.im * v.im)).symm
  exact
    Eq.subst
      (motive := fun T : ℝ =>
        (1 - A * B) * (u.re * v.re) ≤ T)
      hre_eq.symm
      hraw

/-- Tangent-addition sector-width step for a product.  The denominator is
written as an inverse so later power induction can carry a scalar recursive
width without relying on division normalization. -/
theorem complex_mul_im_abs_le_sector_width_step
    {u v : ℂ}
    {A B : ℝ}
    (hu_re_nonneg : 0 ≤ u.re)
    (hv_re_nonneg : 0 ≤ v.re)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hu_im : |u.im| ≤ A * u.re)
    (hv_im : |v.im| ≤ B * v.re)
    (hAB_lt : A * B < 1) :
    |(u * v).im| ≤
      ((A + B) * (1 - A * B)⁻¹) * (u * v).re := by
  let D : ℝ := 1 - A * B
  let P : ℝ := u.re * v.re
  let S : ℝ := A + B
  have hD_pos : 0 < D := by
    exact sub_pos.mpr hAB_lt
  have hD_inv_nonneg : 0 ≤ D⁻¹ :=
    inv_nonneg.mpr (le_of_lt hD_pos)
  have hS_nonneg : 0 ≤ S :=
    add_nonneg hA_nonneg hB_nonneg
  have him_sum :
      |(u * v).im| ≤ S * P :=
    complex_mul_im_abs_le_sum_sector_widths
      hu_re_nonneg hv_re_nonneg hA_nonneg hB_nonneg hu_im hv_im
  have hre_lower :
      D * P ≤ (u * v).re :=
    complex_mul_re_ge_one_sub_mul_sector_widths
      hu_re_nonneg hv_re_nonneg hA_nonneg hB_nonneg hu_im hv_im
  have hP_le :
      P ≤ D⁻¹ * (u * v).re := by
    have hscaled :
        D⁻¹ * (D * P) ≤ D⁻¹ * (u * v).re :=
      mul_le_mul_of_nonneg_left hre_lower hD_inv_nonneg
    have hleft :
        D⁻¹ * (D * P) = P := by
      calc
        D⁻¹ * (D * P) = (D⁻¹ * D) * P := (mul_assoc D⁻¹ D P).symm
        _ = 1 * P := congrArg (fun T : ℝ => T * P) (inv_mul_cancel₀ hD_pos.ne')
        _ = P := one_mul P
    exact
      Eq.subst
        (motive := fun T : ℝ => T ≤ D⁻¹ * (u * v).re)
        hleft
        hscaled
  have hscaled_width :
      S * P ≤ S * (D⁻¹ * (u * v).re) :=
    mul_le_mul_of_nonneg_left hP_le hS_nonneg
  have htarget :
      S * (D⁻¹ * (u * v).re) =
        (S * D⁻¹) * (u * v).re :=
    (mul_assoc S D⁻¹ (u * v).re).symm
  exact
    le_trans him_sum
      (Eq.subst
        (motive := fun T : ℝ => S * P ≤ T)
        htarget
        hscaled_width)

/-- One successor step for sector-power induction.  The width updates by the
tangent-addition rule and the real-part lower constant gains the positive
factor `1 - A * B`. -/
theorem complex_pow_succ_sector_and_re_lower_step
    {w : ℂ}
    {A B c : ℝ}
    {n : ℕ}
    (hpow_re_nonneg : 0 ≤ (w ^ n).re)
    (hw_re_nonneg : 0 ≤ w.re)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hpow_im : |(w ^ n).im| ≤ A * (w ^ n).re)
    (hw_im : |w.im| ≤ B * w.re)
    (hAB_lt : A * B < 1)
    (hlower : c * w.re ^ n ≤ (w ^ n).re) :
    ((c * (1 - A * B)) * w.re ^ (n + 1) ≤
        (w ^ (n + 1)).re) ∧
      (0 ≤ (w ^ (n + 1)).re) ∧
      (|(w ^ (n + 1)).im| ≤
        (((A + B) * (1 - A * B)⁻¹) *
          (w ^ (n + 1)).re)) := by
  let D : ℝ := 1 - A * B
  let U : ℂ := w ^ n
  have hD_pos : 0 < D :=
    sub_pos.mpr hAB_lt
  have hD_nonneg : 0 ≤ D :=
    le_of_lt hD_pos
  have hprod_re_lower :
      D * (U.re * w.re) ≤ (U * w).re :=
    complex_mul_re_ge_one_sub_mul_sector_widths
      hpow_re_nonneg hw_re_nonneg hA_nonneg hB_nonneg hpow_im hw_im
  have hprod_im :
      |(U * w).im| ≤
        ((A + B) * D⁻¹) * (U * w).re :=
    complex_mul_im_abs_le_sector_width_step
      hpow_re_nonneg hw_re_nonneg hA_nonneg hB_nonneg hpow_im hw_im hAB_lt
  have hpow_succ : w ^ (n + 1) = U * w :=
    pow_succ w n
  have hlow_mul :
      c * w.re ^ n * w.re ≤ U.re * w.re :=
    mul_le_mul_of_nonneg_right hlower hw_re_nonneg
  have hlow_scaled :
      D * (c * w.re ^ n * w.re) ≤ D * (U.re * w.re) :=
    mul_le_mul_of_nonneg_left hlow_mul hD_nonneg
  have hconstant_left :
      (c * D) * w.re ^ (n + 1) =
        D * (c * w.re ^ n * w.re) := by
    have hpow_step :
        w.re ^ (n + 1) = w.re ^ n * w.re :=
      pow_succ w.re n
    calc
      (c * D) * w.re ^ (n + 1) =
          (c * D) * (w.re ^ n * w.re) :=
        congrArg (fun T : ℝ => (c * D) * T) hpow_step
      _ = ((c * D) * w.re ^ n) * w.re :=
        (mul_assoc (c * D) (w.re ^ n) w.re).symm
      _ = ((D * c) * w.re ^ n) * w.re :=
        congrArg (fun T : ℝ => (T * w.re ^ n) * w.re) (mul_comm c D)
      _ = (D * (c * w.re ^ n)) * w.re :=
        congrArg (fun T : ℝ => T * w.re) (mul_assoc D c (w.re ^ n))
      _ = D * (c * w.re ^ n * w.re) :=
        mul_assoc D (c * w.re ^ n) w.re
  have hsucc_lower_raw :
      (c * D) * w.re ^ (n + 1) ≤ (U * w).re :=
    le_trans
      (Eq.subst
        (motive := fun T : ℝ => T ≤ D * (U.re * w.re))
        hconstant_left.symm
        hlow_scaled)
      hprod_re_lower
  have hsucc_nonneg_raw : 0 ≤ (U * w).re := by
    have hzero_le_DU :
        0 ≤ D * (U.re * w.re) :=
      mul_nonneg hD_nonneg (mul_nonneg hpow_re_nonneg hw_re_nonneg)
    exact le_trans hzero_le_DU hprod_re_lower
  have hsucc_lower :
      (c * D) * w.re ^ (n + 1) ≤ (w ^ (n + 1)).re :=
    Eq.subst
      (motive := fun T : ℂ =>
        (c * D) * w.re ^ (n + 1) ≤ T.re)
      hpow_succ.symm
      hsucc_lower_raw
  have hsucc_nonneg :
      0 ≤ (w ^ (n + 1)).re :=
    Eq.subst
      (motive := fun T : ℂ => 0 ≤ T.re)
      hpow_succ.symm
      hsucc_nonneg_raw
  have hsucc_im :
      |(w ^ (n + 1)).im| ≤
        (((A + B) * D⁻¹) * (w ^ (n + 1)).re) :=
    Eq.subst
      (motive := fun T : ℂ =>
        |T.im| ≤ (((A + B) * D⁻¹) * T.re))
      hpow_succ.symm
      hprod_im
  exact ⟨hsucc_lower, hsucc_nonneg, hsucc_im⟩

/-- Scalar tangent-addition width step. -/
noncomputable def sectorPowerWidthStep
    (A B : ℝ) : ℝ :=
  (A + B) * (1 - A * B)⁻¹

/-- Scalar sector width after multiplying `k` equal factors with initial
one-factor width `B`. -/
noncomputable def sectorPowerWidth
    (B : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => sectorPowerWidthStep (sectorPowerWidth B k) B

/-- Accumulated real-part lower constant for the sector-power induction. -/
noncomputable def sectorPowerRealConstant
    (B : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => sectorPowerRealConstant B k * (1 - sectorPowerWidth B k * B)

theorem sectorPowerWidth_zero
    (B : ℝ) :
    sectorPowerWidth B 0 = 0 := by
  rfl

theorem sectorPowerWidth_succ
    (B : ℝ)
    (k : ℕ) :
    sectorPowerWidth B (k + 1) =
      sectorPowerWidthStep (sectorPowerWidth B k) B := by
  rfl

theorem sectorPowerRealConstant_zero
    (B : ℝ) :
    sectorPowerRealConstant B 0 = 1 := by
  rfl

theorem sectorPowerRealConstant_succ
    (B : ℝ)
    (k : ℕ) :
    sectorPowerRealConstant B (k + 1) =
      sectorPowerRealConstant B k *
        (1 - sectorPowerWidth B k * B) := by
  rfl

theorem sectorPowerWidthStep_nonneg
    {A B : ℝ}
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hAB_lt : A * B < 1) :
    0 ≤ sectorPowerWidthStep A B := by
  have hsum_nonneg : 0 ≤ A + B :=
    add_nonneg hA_nonneg hB_nonneg
  have hden_pos : 0 < 1 - A * B :=
    sub_pos.mpr hAB_lt
  have hinv_nonneg : 0 ≤ (1 - A * B)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hden_pos)
  exact mul_nonneg hsum_nonneg hinv_nonneg

/-- A denominator-margin form of the tangent-width step bound. -/
theorem sectorPowerWidthStep_le_of_denominator_margin
    {A B L : ℝ}
    (hAB_lt : A * B < 1)
    (hmargin : A + B ≤ L * (1 - A * B)) :
    sectorPowerWidthStep A B ≤ L := by
  let D : ℝ := 1 - A * B
  have hD_pos : 0 < D :=
    sub_pos.mpr hAB_lt
  have hD_inv_nonneg : 0 ≤ D⁻¹ :=
    inv_nonneg.mpr (le_of_lt hD_pos)
  have hscaled :
      (A + B) * D⁻¹ ≤ (L * D) * D⁻¹ :=
    mul_le_mul_of_nonneg_right hmargin hD_inv_nonneg
  have hright :
      (L * D) * D⁻¹ = L := by
    calc
      (L * D) * D⁻¹ = L * (D * D⁻¹) :=
        mul_assoc L D D⁻¹
      _ = L * 1 :=
        congrArg (fun T : ℝ => L * T) (mul_inv_cancel₀ hD_pos.ne')
      _ = L := mul_one L
  exact
    Eq.subst
      (motive := fun T : ℝ => sectorPowerWidthStep A B ≤ T)
      hright
      hscaled

/-- Linear width control and a smallness condition give the subcritical product
needed by the tangent-width recursion. -/
theorem sectorPowerWidth_mul_lt_one_of_le_linear
    {B : ℝ}
    {k : ℕ}
    (hB_nonneg : 0 ≤ B)
    (hwidth :
      sectorPowerWidth B k ≤ 2 * (k : ℝ) * B)
    (hsmall : 2 * (k : ℝ) * B * B < 1) :
    sectorPowerWidth B k * B < 1 := by
  have hscaled :
      sectorPowerWidth B k * B ≤ (2 * (k : ℝ) * B) * B :=
    mul_le_mul_of_nonneg_right hwidth hB_nonneg
  have hright_eq :
      (2 * (k : ℝ) * B) * B =
        2 * (k : ℝ) * B * B := by
    rfl
  exact
    lt_of_le_of_lt
      (Eq.subst
        (motive := fun T : ℝ => sectorPowerWidth B k * B ≤ T)
        hright_eq
        hscaled)
      hsmall

/-- Linear width control is nonnegative when the slope is nonnegative and the
width itself has already been propagated nonnegative. -/
theorem sectorPowerWidth_nonneg_of_previous_step
    {B : ℝ}
    {k : ℕ}
    (hB_nonneg : 0 ≤ B)
    (hprev_nonneg : 0 ≤ sectorPowerWidth B k)
    (hsubcritical : sectorPowerWidth B k * B < 1) :
    0 ≤ sectorPowerWidth B (k + 1) := by
  have hstep_nonneg :
      0 ≤ sectorPowerWidthStep (sectorPowerWidth B k) B :=
    sectorPowerWidthStep_nonneg hprev_nonneg hB_nonneg hsubcritical
  exact
    Eq.subst
      (motive := fun T : ℝ => 0 ≤ T)
      (sectorPowerWidth_succ B k).symm
      hstep_nonneg

/-- Linear control of the tangent-width recursion from explicit denominator
margins at each successor step. -/
theorem sectorPowerWidth_le_linear_of_step_margins
    (B : ℝ)
    (hB_nonneg : 0 ≤ B) :
    ∀ n : ℕ,
      (∀ k : ℕ, k < n →
        2 * (k : ℝ) * B * B < 1) →
      (∀ k : ℕ, k < n →
        sectorPowerWidth B k + B ≤
          (2 * ((k + 1 : ℕ) : ℝ) * B) *
            (1 - sectorPowerWidth B k * B)) →
      (∀ k : ℕ, k ≤ n → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
        (∀ k : ℕ, k ≤ n → 0 ≤ sectorPowerWidth B k) ∧
        (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1)
  | 0, _, _ => by
      have hwidth0 :
          sectorPowerWidth B 0 ≤ 2 * (0 : ℝ) * B := by
        have hleft : sectorPowerWidth B 0 = 0 :=
          sectorPowerWidth_zero B
        have hright : 2 * (0 : ℝ) * B = 0 := by
          calc
            2 * (0 : ℝ) * B = 0 * B := by
              rfl
            _ = 0 := zero_mul B
        exact
          Eq.subst
            (motive := fun T : ℝ => T ≤ 2 * (0 : ℝ) * B)
            hleft
            (Eq.subst
              (motive := fun T : ℝ => 0 ≤ T)
              hright.symm
              (le_of_eq rfl))
      have hnonneg0 :
          0 ≤ sectorPowerWidth B 0 :=
        Eq.subst
          (motive := fun T : ℝ => 0 ≤ T)
          (sectorPowerWidth_zero B).symm
          (le_of_eq rfl)
      exact
        ⟨fun k hk =>
          match Nat.eq_zero_of_le_zero hk with
          | rfl => hwidth0,
         fun k hk =>
          match Nat.eq_zero_of_le_zero hk with
          | rfl => hnonneg0,
         fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | n + 1, hsmall, hmargin => by
      have hsmall_prev :
          ∀ k : ℕ, k < n → 2 * (k : ℝ) * B * B < 1 :=
        fun k hk =>
          hsmall k (lt_trans hk (Nat.lt_succ_self n))
      have hmargin_prev :
          ∀ k : ℕ, k < n →
            sectorPowerWidth B k + B ≤
              (2 * ((k + 1 : ℕ) : ℝ) * B) *
                (1 - sectorPowerWidth B k * B) :=
        fun k hk =>
          hmargin k (lt_trans hk (Nat.lt_succ_self n))
      have hprev :
          (∀ k : ℕ, k ≤ n → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
            (∀ k : ℕ, k ≤ n → 0 ≤ sectorPowerWidth B k) ∧
            (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1) :=
        sectorPowerWidth_le_linear_of_step_margins
          B hB_nonneg n hsmall_prev hmargin_prev
      have hn_width :
          sectorPowerWidth B n ≤ 2 * (n : ℝ) * B :=
        hprev.1 n le_rfl
      have hn_subcritical :
          sectorPowerWidth B n * B < 1 :=
        sectorPowerWidth_mul_lt_one_of_le_linear
          hB_nonneg hn_width (hsmall n (Nat.lt_succ_self n))
      have hsucc_width :
          sectorPowerWidth B (n + 1) ≤
            2 * ((n + 1 : ℕ) : ℝ) * B := by
        have hstep :
            sectorPowerWidthStep (sectorPowerWidth B n) B ≤
              2 * ((n + 1 : ℕ) : ℝ) * B :=
          sectorPowerWidthStep_le_of_denominator_margin
            hn_subcritical (hmargin n (Nat.lt_succ_self n))
        exact
          Eq.subst
            (motive := fun T : ℝ =>
              T ≤ 2 * ((n + 1 : ℕ) : ℝ) * B)
            (sectorPowerWidth_succ B n).symm
            hstep
      have hsucc_nonneg :
          0 ≤ sectorPowerWidth B (n + 1) :=
        sectorPowerWidth_nonneg_of_previous_step
          hB_nonneg (hprev.2.1 n le_rfl) hn_subcritical
      exact
        ⟨fun k hk =>
          match Nat.eq_or_lt_of_le hk with
          | Or.inl heq =>
              Eq.subst
                (motive := fun T : ℕ =>
                  sectorPowerWidth B k ≤ 2 * (T : ℝ) * B)
                heq.symm
                hsucc_width
          | Or.inr hlt =>
              hprev.1 k (Nat.le_of_lt_succ hlt),
         fun k hk =>
          match Nat.eq_or_lt_of_le hk with
          | Or.inl heq =>
              Eq.subst
                (motive := fun T : ℕ => 0 ≤ sectorPowerWidth B T)
                heq
                hsucc_nonneg
          | Or.inr hlt =>
              hprev.2.1 k (Nat.le_of_lt_succ hlt),
         fun k hk =>
          match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
          | Or.inl heq =>
              Eq.subst
                (motive := fun T : ℕ => sectorPowerWidth B T * B < 1)
                heq
                hn_subcritical
          | Or.inr hlt =>
              hprev.2.2 k hlt⟩

theorem sectorPowerRealConstant_pos_of_subcritical_steps
    (B : ℝ) :
    ∀ n : ℕ,
      (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1) →
      0 < sectorPowerRealConstant B n
  | 0, _ => by
      exact Eq.subst
        (motive := fun T : ℝ => 0 < T)
        (sectorPowerRealConstant_zero B).symm
        zero_lt_one
  | n + 1, hsteps => by
      have hprev_steps :
          ∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1 :=
        fun k hk =>
          hsteps k (lt_trans hk (Nat.lt_succ_self n))
      have hprev_pos :
          0 < sectorPowerRealConstant B n :=
        sectorPowerRealConstant_pos_of_subcritical_steps B n hprev_steps
      have hfactor_pos :
          0 < 1 - sectorPowerWidth B n * B :=
        sub_pos.mpr (hsteps n (Nat.lt_succ_self n))
      have hprod_pos :
          0 <
            sectorPowerRealConstant B n *
              (1 - sectorPowerWidth B n * B) :=
        mul_pos hprev_pos hfactor_pos
      exact Eq.subst
        (motive := fun T : ℝ => 0 < T)
        (sectorPowerRealConstant_succ B n).symm
        hprod_pos

/-- Positive accumulated real-part constant from the same linear tangent-width
recursion package. -/
theorem sectorPowerRealConstant_pos_of_step_margins
    (B : ℝ)
    (n : ℕ)
    (hB_nonneg : 0 ≤ B)
    (hsmall :
      ∀ k : ℕ, k < n →
        2 * (k : ℝ) * B * B < 1)
    (hmargin :
      ∀ k : ℕ, k < n →
        sectorPowerWidth B k + B ≤
          (2 * ((k + 1 : ℕ) : ℝ) * B) *
            (1 - sectorPowerWidth B k * B)) :
    0 < sectorPowerRealConstant B n := by
  have hpack :
      (∀ k : ℕ, k ≤ n → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
        (∀ k : ℕ, k ≤ n → 0 ≤ sectorPowerWidth B k) ∧
        (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1) :=
    sectorPowerWidth_le_linear_of_step_margins B hB_nonneg n hsmall hmargin
  exact
    sectorPowerRealConstant_pos_of_subcritical_steps B n hpack.2.2

/-- Generic arbitrary-degree sector-power induction.  The scalar hypotheses are
exactly the tangent-width recursion invariants; the fixed degree-dependent
base supplies them with `B = (2 * (N + 1))⁻¹`. -/
theorem complex_pow_sector_and_re_lower_of_scalar_widths
    {w : ℂ}
    {B : ℝ}
    (hw_re_nonneg : 0 ≤ w.re)
    (hB_nonneg : 0 ≤ B)
    (hw_im : |w.im| ≤ B * w.re) :
    ∀ n : ℕ,
      (∀ k : ℕ, k < n → 0 ≤ sectorPowerWidth B k) →
      (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1) →
      (sectorPowerRealConstant B n * w.re ^ n ≤ (w ^ n).re) ∧
        (0 ≤ (w ^ n).re) ∧
        (|(w ^ n).im| ≤ sectorPowerWidth B n * (w ^ n).re)
  | 0, _, _ => by
      have hpow_zero : w ^ (0 : ℕ) = 1 := pow_zero w
      have hre_zero : (w ^ (0 : ℕ)).re = 1 :=
        congrArg Complex.re hpow_zero
      have him_zero : (w ^ (0 : ℕ)).im = 0 :=
        congrArg Complex.im hpow_zero
      have hconst_zero : sectorPowerRealConstant B 0 = 1 :=
        sectorPowerRealConstant_zero B
      have hwidth_zero : sectorPowerWidth B 0 = 0 :=
        sectorPowerWidth_zero B
      have hlower : sectorPowerRealConstant B 0 * w.re ^ (0 : ℕ) ≤
          (w ^ (0 : ℕ)).re := by
        have hleft :
            sectorPowerRealConstant B 0 * w.re ^ (0 : ℕ) = 1 := by
          calc
            sectorPowerRealConstant B 0 * w.re ^ (0 : ℕ) =
                1 * w.re ^ (0 : ℕ) :=
              congrArg (fun T : ℝ => T * w.re ^ (0 : ℕ)) hconst_zero
            _ = 1 * 1 := congrArg (fun T : ℝ => 1 * T) (pow_zero w.re)
            _ = 1 := one_mul 1
        exact
          Eq.subst
            (motive := fun T : ℝ => T ≤ (w ^ (0 : ℕ)).re)
            hleft
            (Eq.subst
              (motive := fun T : ℝ => 1 ≤ T)
              hre_zero.symm
              (le_of_eq rfl))
      have hre_nonneg : 0 ≤ (w ^ (0 : ℕ)).re :=
        Eq.subst
          (motive := fun T : ℝ => 0 ≤ T)
          hre_zero.symm
          zero_le_one
      have him_bound :
          |(w ^ (0 : ℕ)).im| ≤
            sectorPowerWidth B 0 * (w ^ (0 : ℕ)).re := by
        have hleft_abs : |(w ^ (0 : ℕ)).im| = 0 := by
          calc
            |(w ^ (0 : ℕ)).im| = |0| :=
              congrArg (fun T : ℝ => |T|) him_zero
            _ = 0 := abs_zero
        have hright_zero :
            sectorPowerWidth B 0 * (w ^ (0 : ℕ)).re = 0 := by
          calc
            sectorPowerWidth B 0 * (w ^ (0 : ℕ)).re =
                0 * (w ^ (0 : ℕ)).re :=
              congrArg (fun T : ℝ => T * (w ^ (0 : ℕ)).re) hwidth_zero
            _ = 0 := zero_mul (w ^ (0 : ℕ)).re
        exact
          Eq.subst
            (motive := fun T : ℝ => T ≤ sectorPowerWidth B 0 * (w ^ (0 : ℕ)).re)
            hleft_abs
            (Eq.subst
              (motive := fun T : ℝ => 0 ≤ T)
              hright_zero.symm
              (le_of_eq rfl))
      exact ⟨hlower, hre_nonneg, him_bound⟩
  | n + 1, hwidth_nonneg, hwidth_subcritical => by
      have hprev_nonneg :
          ∀ k : ℕ, k < n → 0 ≤ sectorPowerWidth B k :=
        fun k hk =>
          hwidth_nonneg k (lt_trans hk (Nat.lt_succ_self n))
      have hprev_subcritical :
          ∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1 :=
        fun k hk =>
          hwidth_subcritical k (lt_trans hk (Nat.lt_succ_self n))
      have hprev :
          (sectorPowerRealConstant B n * w.re ^ n ≤ (w ^ n).re) ∧
            (0 ≤ (w ^ n).re) ∧
            (|(w ^ n).im| ≤ sectorPowerWidth B n * (w ^ n).re) :=
        complex_pow_sector_and_re_lower_of_scalar_widths
          hw_re_nonneg hB_nonneg hw_im n hprev_nonneg hprev_subcritical
      have hA_nonneg : 0 ≤ sectorPowerWidth B n :=
        hwidth_nonneg n (Nat.lt_succ_self n)
      have hAB_lt : sectorPowerWidth B n * B < 1 :=
        hwidth_subcritical n (Nat.lt_succ_self n)
      have hstep :
          ((sectorPowerRealConstant B n *
              (1 - sectorPowerWidth B n * B)) * w.re ^ (n + 1) ≤
              (w ^ (n + 1)).re) ∧
            (0 ≤ (w ^ (n + 1)).re) ∧
            (|(w ^ (n + 1)).im| ≤
              (((sectorPowerWidth B n + B) *
                (1 - sectorPowerWidth B n * B)⁻¹) *
                (w ^ (n + 1)).re)) :=
        complex_pow_succ_sector_and_re_lower_step
          hprev.2.1 hw_re_nonneg hA_nonneg hB_nonneg hprev.2.2 hw_im hAB_lt
          hprev.1
      have hconst_succ :
          sectorPowerRealConstant B (n + 1) =
            sectorPowerRealConstant B n *
              (1 - sectorPowerWidth B n * B) :=
        sectorPowerRealConstant_succ B n
      have hwidth_succ :
          sectorPowerWidth B (n + 1) =
            (sectorPowerWidth B n + B) *
              (1 - sectorPowerWidth B n * B)⁻¹ :=
        sectorPowerWidth_succ B n
      have hlower :
          sectorPowerRealConstant B (n + 1) * w.re ^ (n + 1) ≤
            (w ^ (n + 1)).re :=
        Eq.subst
          (motive := fun T : ℝ => T * w.re ^ (n + 1) ≤ (w ^ (n + 1)).re)
          hconst_succ.symm
          hstep.1
      have him_bound :
          |(w ^ (n + 1)).im| ≤
            sectorPowerWidth B (n + 1) * (w ^ (n + 1)).re :=
        Eq.subst
          (motive := fun T : ℝ =>
            |(w ^ (n + 1)).im| ≤ T * (w ^ (n + 1)).re)
          hwidth_succ.symm
          hstep.2.2
      exact ⟨hlower, hstep.2.1, him_bound⟩

/-- Arbitrary-degree sector-power lower bound from explicit scalar
tangent-width margins. -/
theorem complex_pow_sector_and_re_lower_of_step_margins
    {w : ℂ}
    {B : ℝ}
    (n : ℕ)
    (hw_re_nonneg : 0 ≤ w.re)
    (hB_nonneg : 0 ≤ B)
    (hw_im : |w.im| ≤ B * w.re)
    (hsmall :
      ∀ k : ℕ, k < n →
        2 * (k : ℝ) * B * B < 1)
    (hmargin :
      ∀ k : ℕ, k < n →
        sectorPowerWidth B k + B ≤
          (2 * ((k + 1 : ℕ) : ℝ) * B) *
            (1 - sectorPowerWidth B k * B)) :
    (sectorPowerRealConstant B n * w.re ^ n ≤ (w ^ n).re) ∧
      (0 ≤ (w ^ n).re) ∧
      (|(w ^ n).im| ≤ sectorPowerWidth B n * (w ^ n).re) := by
  have hpack :
      (∀ k : ℕ, k ≤ n → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
        (∀ k : ℕ, k ≤ n → 0 ≤ sectorPowerWidth B k) ∧
        (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1) :=
    sectorPowerWidth_le_linear_of_step_margins B hB_nonneg n hsmall hmargin
  exact
    complex_pow_sector_and_re_lower_of_scalar_widths
      hw_re_nonneg hB_nonneg hw_im n
      (fun k hk => hpack.2.1 k (le_of_lt hk))
      hpack.2.2

/-- The scaled tilted-coordinate argument remains in the fixed sector
`|arg| ≤ π / 4` on the closed vertical strip. -/
theorem verticalStripUpperTailDamping_scaledBase_im_abs_le_pi_div_four
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    |verticalStripUpperTailDampingScale a b *
        (verticalStripUpperTailDampingBase a b z).im| ≤
      π / 4 := by
  let M : ℝ := 2 * (|a| + |b| + 2)
  let s : ℝ := verticalStripUpperTailDampingScale a b
  have hsum_nonneg : 0 ≤ |a| + |b| :=
    add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hinner_pos : 0 < |a| + |b| + 2 :=
    lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_left hsum_nonneg)
  have hM_pos : 0 < M :=
    mul_pos zero_lt_two hinner_pos
  have hM_nonneg : 0 ≤ M :=
    le_of_lt hM_pos
  have hs_pos : 0 < s :=
    verticalStripUpperTailDampingScale_pos a b
  have hs_nonneg : 0 ≤ s :=
    le_of_lt hs_pos
  have him :
      |(verticalStripUpperTailDampingBase a b z).im| ≤ M :=
    verticalStripUpperTailDampingBase_im_abs_le a b hza hzb
  have habs_mul :
      |s * (verticalStripUpperTailDampingBase a b z).im| =
        s * |(verticalStripUpperTailDampingBase a b z).im| := by
    calc
      |s * (verticalStripUpperTailDampingBase a b z).im| =
          |s| * |(verticalStripUpperTailDampingBase a b z).im| :=
        abs_mul s ((verticalStripUpperTailDampingBase a b z).im)
      _ = s * |(verticalStripUpperTailDampingBase a b z).im| := by
        exact congrArg
          (fun x : ℝ => x * |(verticalStripUpperTailDampingBase a b z).im|)
          (abs_of_nonneg hs_nonneg)
  have hmul_le : s * |(verticalStripUpperTailDampingBase a b z).im| ≤ s * M :=
    mul_le_mul_of_nonneg_left him hs_nonneg
  have hscale_mul :
      s * M = π / 4 := by
    have hM_ne : M ≠ 0 :=
      ne_of_gt hM_pos
    have hden_ne : 4 * M ≠ 0 :=
      mul_ne_zero (show (4 : ℝ) ≠ 0 from ne_of_gt zero_lt_four) hM_ne
    calc
      s * M =
          (π / (4 * M)) * M := rfl
      _ = π / 4 := by
        calc
          (π / (4 * M)) * M =
              π * M / (4 * M) := by
            exact div_mul_eq_mul_div π (4 * M) M
          _ = π * M / (M * 4) := by
            exact congrArg (fun x : ℝ => π * M / x) (mul_comm 4 M)
          _ = π / 4 := by
            exact mul_div_mul_right π 4 hM_ne
  exact
    le_trans
      (le_of_eq habs_mul)
      (le_trans hmul_le (le_of_eq hscale_mul))

/-- The sector bound in interval form for the real argument of the outer
exponential. -/
theorem verticalStripUpperTailDamping_scaledBase_im_mem_cosineWindow
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    verticalStripUpperTailDampingScale a b *
        (verticalStripUpperTailDampingBase a b z).im ∈
      Set.Icc (-(π / 2)) (π / 2) := by
  let x : ℝ :=
    verticalStripUpperTailDampingScale a b *
      (verticalStripUpperTailDampingBase a b z).im
  have hx_abs : |x| ≤ π / 4 :=
    verticalStripUpperTailDamping_scaledBase_im_abs_le_pi_div_four
      a b hza hzb
  have hx_bounds : -(π / 4) ≤ x ∧ x ≤ π / 4 :=
    abs_le.mp hx_abs
  have htwo_le_four : (2 : ℝ) ≤ 4 := by
    calc
      (2 : ℝ) ≤ 2 + 2 := le_add_of_nonneg_right zero_le_two
      _ = 4 := two_add_two_eq_four
  have hpi_div_four_le_pi_div_two : π / 4 ≤ π / 2 :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) zero_lt_two htwo_le_four
  have hneg_pi_div_two_le_neg_pi_div_four : -(π / 2) ≤ -(π / 4) :=
    neg_le_neg hpi_div_four_le_pi_div_two
  exact
    ⟨le_trans hneg_pi_div_two_le_neg_pi_div_four hx_bounds.1,
      le_trans hx_bounds.2 hpi_div_four_le_pi_div_two⟩

/-- Real-part formula for the tilted upper-tail damping kernel. -/
theorem verticalStripUpperTailDampingKernel_re_eq
    (a b : ℝ)
    (z : ℂ) :
    (verticalStripUpperTailDampingKernel a b z).re =
      Real.exp
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).re) *
        Real.cos
          (verticalStripUpperTailDampingScale a b *
            (verticalStripUpperTailDampingBase a b z).im) := by
  let s : ℝ := verticalStripUpperTailDampingScale a b
  let W : ℂ := verticalStripUpperTailDampingBase a b z
  have hmul_re : (((s : ℂ) * W).re) = s * W.re := by
    calc
      (((s : ℂ) * W).re) =
          (s : ℂ).re * W.re - (s : ℂ).im * W.im :=
        Complex.mul_re (s : ℂ) W
      _ = s * W.re - 0 * W.im := by
        exact congrArg₂
          (fun x y : ℝ => x * W.re - y * W.im)
          (Complex.ofReal_re s)
          (Complex.ofReal_im s)
      _ = s * W.re - 0 := by
        exact congrArg (fun x : ℝ => s * W.re - x) (zero_mul W.im)
      _ = s * W.re := sub_zero (s * W.re)
  have hmul_im : (((s : ℂ) * W).im) = s * W.im := by
    calc
      (((s : ℂ) * W).im) =
          (s : ℂ).re * W.im + (s : ℂ).im * W.re :=
        Complex.mul_im (s : ℂ) W
      _ = s * W.im + 0 * W.re := by
        exact congrArg₂
          (fun x y : ℝ => x * W.im + y * W.re)
          (Complex.ofReal_re s)
          (Complex.ofReal_im s)
      _ = s * W.im + 0 := by
        exact congrArg (fun x : ℝ => s * W.im + x) (zero_mul W.re)
      _ = s * W.im := add_zero (s * W.im)
  calc
    (verticalStripUpperTailDampingKernel a b z).re =
        (Complex.exp ((s : ℂ) * W)).re := rfl
    _ = Real.exp (((s : ℂ) * W).re) *
        Real.cos (((s : ℂ) * W).im) :=
      Complex.exp_re ((s : ℂ) * W)
    _ = Real.exp (s * W.re) * Real.cos (s * W.im) := by
      exact congrArg₂ HMul.hMul
        (congrArg Real.exp hmul_re)
        (congrArg Real.cos hmul_im)
    _ =
      Real.exp
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).re) *
        Real.cos
          (verticalStripUpperTailDampingScale a b *
            (verticalStripUpperTailDampingBase a b z).im) := rfl

/-- The tilted upper-tail damping kernel has nonnegative real part on the
closed vertical strip. -/
theorem verticalStripUpperTailDampingKernel_re_nonneg_on_closedStrip
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    0 ≤ (verticalStripUpperTailDampingKernel a b z).re := by
  have hcos : 0 ≤
      Real.cos
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).im) :=
    Real.cos_nonneg_of_mem_Icc
      (verticalStripUpperTailDamping_scaledBase_im_mem_cosineWindow
        a b hza hzb)
  have hexp : 0 ≤
      Real.exp
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).re) :=
    le_of_lt
      (Real.exp_pos
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).re))
  have hproduct :
      0 ≤
        Real.exp
          (verticalStripUpperTailDampingScale a b *
            (verticalStripUpperTailDampingBase a b z).re) *
          Real.cos
            (verticalStripUpperTailDampingScale a b *
              (verticalStripUpperTailDampingBase a b z).im) :=
    mul_nonneg hexp hcos
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (verticalStripUpperTailDampingKernel_re_eq a b z).symm
      hproduct

/-- The tilted upper-tail damping kernel has strictly positive real part on
the closed vertical strip.  The scale choice puts the argument of the outer
exponential in `[-π/4, π/4]`, strictly inside the positive-cosine window. -/
theorem verticalStripUpperTailDampingKernel_re_pos_on_closedStrip
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    0 < (verticalStripUpperTailDampingKernel a b z).re := by
  let x : ℝ :=
    verticalStripUpperTailDampingScale a b *
      (verticalStripUpperTailDampingBase a b z).im
  have hx_abs : |x| ≤ π / 4 :=
    verticalStripUpperTailDamping_scaledBase_im_abs_le_pi_div_four
      a b hza hzb
  have hx_bounds : -(π / 4) ≤ x ∧ x ≤ π / 4 :=
    abs_le.mp hx_abs
  have htwo_lt_four : (2 : ℝ) < 4 :=
    Nat.cast_lt.mpr
      (show (2 : ℕ) < 4 from
        Nat.succ_lt_succ
          (Nat.succ_lt_succ
            (Nat.zero_lt_succ 1)))
  have hpi_div_four_lt_pi_div_two : π / 4 < π / 2 :=
    div_lt_div_of_pos_left Real.pi_pos zero_lt_two htwo_lt_four
  have hx_mem : x ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨lt_of_lt_of_le
        (neg_lt_neg hpi_div_four_lt_pi_div_two)
        hx_bounds.1,
      lt_of_le_of_lt hx_bounds.2 hpi_div_four_lt_pi_div_two⟩
  have hcos : 0 <
      Real.cos
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).im) :=
    Real.cos_pos_of_mem_Ioo hx_mem
  have hexp : 0 <
      Real.exp
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).re) :=
    Real.exp_pos
      (verticalStripUpperTailDampingScale a b *
        (verticalStripUpperTailDampingBase a b z).re)
  have hproduct :
      0 <
        Real.exp
          (verticalStripUpperTailDampingScale a b *
            (verticalStripUpperTailDampingBase a b z).re) *
          Real.cos
            (verticalStripUpperTailDampingScale a b *
              (verticalStripUpperTailDampingBase a b z).im) :=
    mul_pos hexp hcos
  exact
    Eq.subst
      (motive := fun y : ℝ => 0 < y)
      (verticalStripUpperTailDampingKernel_re_eq a b z).symm
      hproduct

/-- The cosine factor in the tilted upper-tail damping kernel is uniformly
bounded below by its endpoint value on `[-π/4, π/4]`. -/
theorem verticalStripUpperTailDamping_cos_lower_bound
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    Real.sqrt 2 / 2 ≤
      Real.cos
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).im) := by
  let x : ℝ :=
    verticalStripUpperTailDampingScale a b *
      (verticalStripUpperTailDampingBase a b z).im
  have hx_abs : |x| ≤ π / 4 :=
    verticalStripUpperTailDamping_scaledBase_im_abs_le_pi_div_four
      a b hza hzb
  have htwo_lt_four : (2 : ℝ) < 4 :=
    Nat.cast_lt.mpr
      (show (2 : ℕ) < 4 from
        Nat.succ_lt_succ
          (Nat.succ_lt_succ
            (Nat.zero_lt_succ 1)))
  have hpi_div_four_lt_pi_div_two : π / 4 < π / 2 :=
    div_lt_div_of_pos_left Real.pi_pos zero_lt_two htwo_lt_four
  have hpi_div_four_le_pi : π / 4 ≤ π := by
    have hpi_div_two_le_pi : π / 2 ≤ π :=
      (div_le_self Real.pi_pos.le one_le_two)
    exact le_trans (le_of_lt hpi_div_four_lt_pi_div_two) hpi_div_two_le_pi
  have hcos_endpoint_le_abs :
      Real.cos (π / 4) ≤ Real.cos |x| :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg x)
      hpi_div_four_le_pi
      hx_abs
  have hcos_abs :
      Real.cos |x| = Real.cos x :=
    Real.cos_abs x
  have hcos_endpoint :
      Real.sqrt 2 / 2 = Real.cos (π / 4) :=
    (Real.cos_pi_div_four).symm
  exact
    Eq.subst
      (motive := fun y : ℝ => y ≤ Real.cos x)
      hcos_endpoint
      (Eq.subst
        (motive := fun y : ℝ => Real.cos (π / 4) ≤ y)
        hcos_abs
        hcos_endpoint_le_abs)

/-- Quantitative real-part lower bound for the tilted upper-tail damping
kernel on the closed strip. -/
theorem verticalStripUpperTailDampingKernel_re_lower_bound
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    (Real.sqrt 2 / 2) *
        Real.exp
          (verticalStripUpperTailDampingScale a b *
            (verticalStripUpperTailDampingBase a b z).re) ≤
      (verticalStripUpperTailDampingKernel a b z).re := by
  let E : ℝ :=
    Real.exp
      (verticalStripUpperTailDampingScale a b *
        (verticalStripUpperTailDampingBase a b z).re)
  let C : ℝ :=
    Real.cos
      (verticalStripUpperTailDampingScale a b *
        (verticalStripUpperTailDampingBase a b z).im)
  have hcos : Real.sqrt 2 / 2 ≤ C :=
    verticalStripUpperTailDamping_cos_lower_bound a b hza hzb
  have hE_nonneg : 0 ≤ E :=
    le_of_lt
      (Real.exp_pos
        (verticalStripUpperTailDampingScale a b *
          (verticalStripUpperTailDampingBase a b z).re))
  have hscaled : E * (Real.sqrt 2 / 2) ≤ E * C :=
    mul_le_mul_of_nonneg_left hcos hE_nonneg
  have hleft_comm :
      E * (Real.sqrt 2 / 2) =
        (Real.sqrt 2 / 2) * E :=
    mul_comm E (Real.sqrt 2 / 2)
  have hkernel :
      (verticalStripUpperTailDampingKernel a b z).re = E * C :=
    verticalStripUpperTailDampingKernel_re_eq a b z
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        (Real.sqrt 2 / 2) *
            Real.exp
              (verticalStripUpperTailDampingScale a b *
                (verticalStripUpperTailDampingBase a b z).re) ≤ y)
      hkernel.symm
      (Eq.subst
        (motive := fun y : ℝ => y ≤ E * C)
        hleft_comm
        hscaled)

/-- Quantitative real-part lower bound for the tilted upper-tail damping
kernel, with the upper-tail real coordinate of the tilted base exposed. -/
theorem verticalStripUpperTailDampingKernel_re_lower_bound_explicit
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    (Real.sqrt 2 / 2) *
        Real.exp
          (verticalStripUpperTailDampingScale a b *
            (|a| + |b| + 2 + z.im)) ≤
      (verticalStripUpperTailDampingKernel a b z).re := by
  have hbase :
      (verticalStripUpperTailDampingBase a b z).re =
        |a| + |b| + 2 + z.im :=
    verticalStripUpperTailDampingBase_re a b z
  have hraw :
      (Real.sqrt 2 / 2) *
          Real.exp
            (verticalStripUpperTailDampingScale a b *
              (verticalStripUpperTailDampingBase a b z).re) ≤
        (verticalStripUpperTailDampingKernel a b z).re :=
    verticalStripUpperTailDampingKernel_re_lower_bound a b hza hzb
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        (Real.sqrt 2 / 2) *
            Real.exp (verticalStripUpperTailDampingScale a b * y) ≤
          (verticalStripUpperTailDampingKernel a b z).re)
      hbase
      hraw

/-- Real part of the upper-tail damping exponent. -/
theorem verticalStripUpperTailDampingExponent_re
    (a b ε : ℝ)
    (z : ℂ) :
    (-((ε : ℝ) : ℂ) *
        verticalStripUpperTailDampingKernel a b z).re =
      -ε * (verticalStripUpperTailDampingKernel a b z).re := by
  calc
    (-((ε : ℝ) : ℂ) *
        verticalStripUpperTailDampingKernel a b z).re =
        (-((ε : ℝ) : ℂ)).re *
            (verticalStripUpperTailDampingKernel a b z).re -
          (-((ε : ℝ) : ℂ)).im *
            (verticalStripUpperTailDampingKernel a b z).im := by
      exact
        Complex.mul_re
          (-((ε : ℝ) : ℂ))
          (verticalStripUpperTailDampingKernel a b z)
    _ =
        (-ε) * (verticalStripUpperTailDampingKernel a b z).re -
          (0 : ℝ) * (verticalStripUpperTailDampingKernel a b z).im := by
      exact congrArg₂
        (fun x y : ℝ =>
          x * (verticalStripUpperTailDampingKernel a b z).re -
            y * (verticalStripUpperTailDampingKernel a b z).im)
        (calc
          (-((ε : ℝ) : ℂ)).re = -(((ε : ℝ) : ℂ).re) :=
            Complex.neg_re ((ε : ℝ) : ℂ)
          _ = -ε := congrArg Neg.neg (Complex.ofReal_re ε))
        (calc
          (-((ε : ℝ) : ℂ)).im = -(((ε : ℝ) : ℂ).im) :=
            Complex.neg_im ((ε : ℝ) : ℂ)
          _ = -0 := congrArg Neg.neg (Complex.ofReal_im ε)
          _ = 0 := neg_zero)
    _ = (-ε) * (verticalStripUpperTailDampingKernel a b z).re - 0 := by
      exact congrArg
        (fun y : ℝ =>
          (-ε) * (verticalStripUpperTailDampingKernel a b z).re - y)
        (zero_mul (verticalStripUpperTailDampingKernel a b z).im)
    _ = (-ε) * (verticalStripUpperTailDampingKernel a b z).re := by
      exact sub_zero ((-ε) * (verticalStripUpperTailDampingKernel a b z).re)
    _ = -(ε * (verticalStripUpperTailDampingKernel a b z).re) := by
      exact neg_mul ε (verticalStripUpperTailDampingKernel a b z).re
    _ = -ε * (verticalStripUpperTailDampingKernel a b z).re := by
      exact (neg_mul ε (verticalStripUpperTailDampingKernel a b z).re).symm

/-- The upper-tail damping exponent has nonpositive real part on the closed
strip. -/
theorem verticalStripUpperTailDampingExponent_re_nonpos_on_closedStrip
    (a b ε : ℝ)
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    (-((ε : ℝ) : ℂ) *
        verticalStripUpperTailDampingKernel a b z).re ≤ 0 := by
  have hkernel_nonneg :
      0 ≤ (verticalStripUpperTailDampingKernel a b z).re :=
    verticalStripUpperTailDampingKernel_re_nonneg_on_closedStrip
      a b hza hzb
  have hproduct_nonneg :
      0 ≤ ε * (verticalStripUpperTailDampingKernel a b z).re :=
    mul_nonneg hε hkernel_nonneg
  have hneg_nonpos :
      -(ε * (verticalStripUpperTailDampingKernel a b z).re) ≤ 0 :=
    neg_nonpos.mpr hproduct_nonneg
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripUpperTailDampingKernel a b z).re =
        -ε * (verticalStripUpperTailDampingKernel a b z).re :=
    verticalStripUpperTailDampingExponent_re a b ε z
  have hneg_mul :
      -ε * (verticalStripUpperTailDampingKernel a b z).re =
        -(ε * (verticalStripUpperTailDampingKernel a b z).re) :=
    neg_mul ε (verticalStripUpperTailDampingKernel a b z).re
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 0)
      (Eq.trans hre hneg_mul).symm
      hneg_nonpos

/-- With positive damping parameter, the upper-tail damping exponent has
strictly negative real part on the closed strip. -/
theorem verticalStripUpperTailDampingExponent_re_neg_on_closedStrip
    (a b ε : ℝ)
    (hε : 0 < ε)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    (-((ε : ℝ) : ℂ) *
        verticalStripUpperTailDampingKernel a b z).re < 0 := by
  have hkernel_pos :
      0 < (verticalStripUpperTailDampingKernel a b z).re :=
    verticalStripUpperTailDampingKernel_re_pos_on_closedStrip
      a b hza hzb
  have hproduct_pos :
      0 < ε * (verticalStripUpperTailDampingKernel a b z).re :=
    mul_pos hε hkernel_pos
  have hneg_neg :
      -(ε * (verticalStripUpperTailDampingKernel a b z).re) < 0 :=
    neg_neg_of_pos hproduct_pos
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripUpperTailDampingKernel a b z).re =
        -ε * (verticalStripUpperTailDampingKernel a b z).re :=
    verticalStripUpperTailDampingExponent_re a b ε z
  have hneg_mul :
      -ε * (verticalStripUpperTailDampingKernel a b z).re =
        -(ε * (verticalStripUpperTailDampingKernel a b z).re) :=
    neg_mul ε (verticalStripUpperTailDampingKernel a b z).re
  exact
    Eq.subst
      (motive := fun x : ℝ => x < 0)
      (Eq.trans hre hneg_mul).symm
      hneg_neg

/-- The tilted upper-tail damping factor has norm at most one on the closed
strip. -/
theorem verticalStripUpperTailDampingFactor_norm_le_one_on_closedStrip
    (a b ε : ℝ)
    (hε : 0 ≤ ε)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripUpperTailDampingKernel a b z)‖ ≤ 1 := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripUpperTailDampingKernel a b z
  have hre_nonpos : w.re ≤ 0 :=
    verticalStripUpperTailDampingExponent_re_nonpos_on_closedStrip
      a b ε hε hza hzb
  have hexp_le_one : Real.exp w.re ≤ 1 :=
    Real.exp_le_one_iff.mpr hre_nonpos
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    Eq.trans (Complex.norm_eq_abs (Complex.exp w)) (Complex.abs_exp w)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      hnorm.symm
      hexp_le_one

/-- With positive damping parameter, the tilted upper-tail damping factor has
norm strictly less than one on the closed strip. -/
theorem verticalStripUpperTailDampingFactor_norm_lt_one_on_closedStrip
    (a b ε : ℝ)
    (hε : 0 < ε)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripUpperTailDampingKernel a b z)‖ < 1 := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripUpperTailDampingKernel a b z
  have hre_neg : w.re < 0 :=
    verticalStripUpperTailDampingExponent_re_neg_on_closedStrip
      a b ε hε hza hzb
  have hexp_lt_one : Real.exp w.re < 1 :=
    Real.exp_lt_one_iff.mpr hre_neg
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    Eq.trans (Complex.norm_eq_abs (Complex.exp w)) (Complex.abs_exp w)
  exact
    Eq.subst
      (motive := fun x : ℝ => x < 1)
      hnorm.symm
      hexp_lt_one

/-- Multiplication by the tilted upper-tail damping factor can only decrease
norms on the closed strip. -/
theorem verticalStripUpperTailDampedFamily_norm_le_original_on_closedStrip
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hε : 0 ≤ ε)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ ‖f z‖ := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripUpperTailDampingKernel a b z)
  have hfactor : ‖g‖ ≤ 1 :=
    verticalStripUpperTailDampingFactor_norm_le_one_on_closedStrip
      a b ε hε z hza hzb
  have hmul_eq :
      ‖verticalStripUpperTailDampedFamily f a b ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripUpperTailDampedFamily f a b ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hscale_nonneg : 0 ≤ ‖f z‖ :=
    norm_nonneg (f z)
  have hscaled : ‖f z‖ * ‖g‖ ≤ ‖f z‖ * 1 :=
    mul_le_mul_of_nonneg_left hfactor hscale_nonneg
  have hright : ‖f z‖ * 1 = ‖f z‖ :=
    mul_one ‖f z‖
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ x)
      hright
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖f z‖ * 1)
        hmul_eq.symm
        hscaled)

/-- Explicit upper-tail decaying bound for the tilted damping factor. -/
theorem verticalStripUpperTailDampingFactor_norm_le_exp_explicit
    (a b ε : ℝ)
    (hε : 0 ≤ ε)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripUpperTailDampingKernel a b z)‖ ≤
      Real.exp
        (-(ε * (Real.sqrt 2 / 2) *
          Real.exp
            (verticalStripUpperTailDampingScale a b *
              (|a| + |b| + 2 + z.im)))) := by
  let K : ℝ := (verticalStripUpperTailDampingKernel a b z).re
  let L : ℝ :=
    (Real.sqrt 2 / 2) *
      Real.exp
        (verticalStripUpperTailDampingScale a b *
          (|a| + |b| + 2 + z.im))
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripUpperTailDampingKernel a b z
  have hL_le_K : L ≤ K :=
    verticalStripUpperTailDampingKernel_re_lower_bound_explicit
      a b hza hzb
  have hmul_le : ε * L ≤ ε * K :=
    mul_le_mul_of_nonneg_left hL_le_K hε
  have hneg_le : -(ε * K) ≤ -(ε * L) :=
    neg_le_neg hmul_le
  have hre :
      w.re = -ε * (verticalStripUpperTailDampingKernel a b z).re :=
    verticalStripUpperTailDampingExponent_re a b ε z
  have hneg_mul :
      -ε * (verticalStripUpperTailDampingKernel a b z).re =
        -(ε * K) :=
    neg_mul ε K
  have hre_le :
      w.re ≤ -(ε * L) :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ -(ε * L))
      (Eq.trans hre hneg_mul).symm
      hneg_le
  have hexp_le :
      Real.exp w.re ≤ Real.exp (-(ε * L)) :=
    Real.exp_le_exp.mpr hre_le
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    Eq.trans (Complex.norm_eq_abs (Complex.exp w)) (Complex.abs_exp w)
  have hmul_assoc :
      ε * L =
        ε * (Real.sqrt 2 / 2) *
          Real.exp
            (verticalStripUpperTailDampingScale a b *
              (|a| + |b| + 2 + z.im)) :=
    mul_assoc ε (Real.sqrt 2 / 2)
      (Real.exp
        (verticalStripUpperTailDampingScale a b *
          (|a| + |b| + 2 + z.im)))
  have htarget_arg :
      -(ε * L) =
        -(ε * (Real.sqrt 2 / 2) *
          Real.exp
            (verticalStripUpperTailDampingScale a b *
              (|a| + |b| + 2 + z.im))) :=
    congrArg Neg.neg hmul_assoc
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripUpperTailDampingKernel a b z)‖ ≤ y)
      (congrArg Real.exp htarget_arg)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ Real.exp (-(ε * L)))
        hnorm.symm
        hexp_le)

/-- A nondegenerate vertical strip has positive width. -/
theorem verticalStripWidth_pos
    {a b : ℝ}
    (hab : a < b) :
    0 < verticalStripWidth a b := by
  exact sub_pos.mpr hab

/-- A nondegenerate vertical strip has nonzero width. -/
theorem verticalStripWidth_ne_zero
    {a b : ℝ}
    (hab : a < b) :
    verticalStripWidth a b ≠ 0 :=
  ne_of_gt (verticalStripWidth_pos hab)

/-- A subcritical strip exponent admits a strictly larger positive cosine-barrier
frequency below the strip threshold.

This is the first scalar choice in the genuine finite-order strip
Phragmen-Lindelöf proof.  The barrier must use a frequency `d < π / (b - a)`,
not the endpoint frequency `π / (b - a)`, so that the cosine factor remains
strictly positive on both vertical boundary lines while still satisfying
`c < d`. -/
theorem exists_verticalStrip_subcritical_cosineBarrier_rate
    {a b c : ℝ}
    (hab : a < b)
    (hc : c < π / (b - a)) :
    ∃ d : ℝ,
      c < d ∧
      0 < d ∧
      d < π / (b - a) := by
  have hwidth_pos : 0 < b - a :=
    sub_pos.mpr hab
  have hthreshold_pos : 0 < π / (b - a) :=
    div_pos Real.pi_pos hwidth_pos
  have hmax_lt : max c 0 < π / (b - a) :=
    max_lt hc hthreshold_pos
  match exists_between hmax_lt with
  | ⟨d, hmax_d, hd_threshold⟩ =>
      have hc_d : c < d :=
        lt_of_le_of_lt (le_max_left c 0) hmax_d
      have hzero_d : 0 < d :=
        lt_of_le_of_lt (le_max_right c 0) hmax_d
      exact ⟨d, hc_d, hzero_d, hd_threshold⟩

/-- The strip center lies halfway from the left endpoint. -/
theorem leftEndpoint_sub_verticalStripCenter
    (a b : ℝ) :
    a - verticalStripCenter a b = (a - b) / 2 := by
  calc
    a - verticalStripCenter a b = a - (a + b) / 2 := rfl
    _ = (2 * a) / 2 - (a + b) / 2 := by
      have htwo_a : (2 * a) / 2 = a := by
        calc
          (2 * a) / 2 = (a * 2) / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (mul_comm 2 a)
          _ = a := by
            exact mul_div_cancel_right₀ a (show (2 : ℝ) ≠ 0 from two_ne_zero)
      exact congrArg (fun x : ℝ => x - (a + b) / 2) htwo_a.symm
    _ = (2 * a - (a + b)) / 2 := by
      exact (sub_div (2 * a) (a + b) 2).symm
    _ = ((a + a) - (a + b)) / 2 := by
      exact congrArg (fun x : ℝ => (x - (a + b)) / 2) (two_mul a)
    _ = (a - b) / 2 := by
      have hnum : (a + a) - (a + b) = a - b := by
        calc
          (a + a) - (a + b) = (a + a) + -(a + b) := by
            exact sub_eq_add_neg (a + a) (a + b)
          _ = (a + a) + (-a + -b) := by
            exact congrArg (fun x : ℝ => (a + a) + x) (neg_add a b)
          _ = a + (a + (-a + -b)) := by
            exact add_assoc a a (-a + -b)
          _ = a + ((a + -a) + -b) := by
            exact congrArg (fun x : ℝ => a + x) (add_assoc a (-a) (-b)).symm
          _ = a + (0 + -b) := by
            exact congrArg (fun x : ℝ => a + (x + -b)) (add_neg_cancel a)
          _ = a + -b := by
            exact congrArg (fun x : ℝ => a + x) (zero_add (-b))
          _ = a - b := by
            exact (sub_eq_add_neg a b).symm
      exact congrArg (fun x : ℝ => x / 2) hnum

/-- The strip center lies halfway from the right endpoint. -/
theorem rightEndpoint_sub_verticalStripCenter
    (a b : ℝ) :
    b - verticalStripCenter a b = (b - a) / 2 := by
  calc
    b - verticalStripCenter a b = b - (a + b) / 2 := rfl
    _ = (2 * b) / 2 - (a + b) / 2 := by
      have htwo_b : (2 * b) / 2 = b := by
        calc
          (2 * b) / 2 = (b * 2) / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (mul_comm 2 b)
          _ = b := by
            exact mul_div_cancel_right₀ b (show (2 : ℝ) ≠ 0 from two_ne_zero)
      exact congrArg (fun x : ℝ => x - (a + b) / 2) htwo_b.symm
    _ = (2 * b - (a + b)) / 2 := by
      exact (sub_div (2 * b) (a + b) 2).symm
    _ = ((b + b) - (a + b)) / 2 := by
      exact congrArg (fun x : ℝ => (x - (a + b)) / 2) (two_mul b)
    _ = (b - a) / 2 := by
      have hnum : (b + b) - (a + b) = b - a := by
        calc
          (b + b) - (a + b) = (b + b) + -(a + b) := by
            exact sub_eq_add_neg (b + b) (a + b)
          _ = (b + b) + (-a + -b) := by
            exact congrArg (fun x : ℝ => (b + b) + x) (neg_add a b)
          _ = b + (b + (-a + -b)) := by
            exact add_assoc b b (-a + -b)
          _ = b + ((b + -b) + -a) := by
            have hinner : b + (-a + -b) = (b + -b) + -a := by
              calc
                b + (-a + -b) = b + (-b + -a) := by
                  exact congrArg (fun x : ℝ => b + x) (add_comm (-a) (-b))
                _ = (b + -b) + -a := by
                  exact (add_assoc b (-b) (-a)).symm
            exact congrArg (fun x : ℝ => b + x) hinner
          _ = b + (0 + -a) := by
            exact congrArg (fun x : ℝ => b + (x + -a)) (add_neg_cancel b)
          _ = b + -a := by
            exact congrArg (fun x : ℝ => b + x) (zero_add (-a))
          _ = b - a := by
            exact (sub_eq_add_neg b a).symm
      exact congrArg (fun x : ℝ => x / 2) hnum

/-- A subcritical cosine-barrier frequency keeps the closed strip inside the
strict positive-cosine window. -/
theorem verticalStrip_subcritical_cosineBarrier_angle_abs_lt_pi_div_two
    {a b d x : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hxa : a ≤ x)
    (hxb : x ≤ b) :
    |d * (x - verticalStripCenter a b)| < π / 2 := by
  let w : ℝ := b - a
  have hw_pos : 0 < w :=
    sub_pos.mpr hab
  have hleft_endpoint :
      a - verticalStripCenter a b = - (w / 2) := by
    calc
      a - verticalStripCenter a b = (a - b) / 2 :=
        leftEndpoint_sub_verticalStripCenter a b
      _ = -((b - a) / 2) := by
        have hnum : a - b = -(b - a) := by
          calc
            a - b = -(b - a) := by
              exact sub_eq_neg_sub a b
        exact
          Eq.trans
            (congrArg (fun t : ℝ => t / 2) hnum)
            (neg_div (b - a) 2).symm
      _ = -(w / 2) := rfl
  have hright_endpoint :
      b - verticalStripCenter a b = w / 2 := by
    calc
      b - verticalStripCenter a b = (b - a) / 2 :=
        rightEndpoint_sub_verticalStripCenter a b
      _ = w / 2 := rfl
  have hleft_bound : -(w / 2) ≤ x - verticalStripCenter a b := by
    have hendpoint_le :
        a - verticalStripCenter a b ≤ x - verticalStripCenter a b :=
      sub_le_sub_right hxa (verticalStripCenter a b)
    exact
      Eq.subst
        (motive := fun t : ℝ => t ≤ x - verticalStripCenter a b)
        hleft_endpoint
        hendpoint_le
  have hright_bound : x - verticalStripCenter a b ≤ w / 2 := by
    have hle_endpoint :
        x - verticalStripCenter a b ≤ b - verticalStripCenter a b :=
      sub_le_sub_right hxb (verticalStripCenter a b)
    exact
      Eq.subst
        (motive := fun t : ℝ => x - verticalStripCenter a b ≤ t)
        hright_endpoint
        hle_endpoint
  have hx_abs : |x - verticalStripCenter a b| ≤ w / 2 :=
    abs_le.mpr ⟨hleft_bound, hright_bound⟩
  have hmul_abs :
      |d * (x - verticalStripCenter a b)| =
        d * |x - verticalStripCenter a b| := by
    calc
      |d * (x - verticalStripCenter a b)| =
          |d| * |x - verticalStripCenter a b| :=
        abs_mul d (x - verticalStripCenter a b)
      _ = d * |x - verticalStripCenter a b| := by
        exact congrArg
          (fun t : ℝ => t * |x - verticalStripCenter a b|)


          (abs_of_pos hd_pos)
  have hd_nonneg : 0 ≤ d :=
    le_of_lt hd_pos
  have hmul_le : d * |x - verticalStripCenter a b| ≤ d * (w / 2) :=
    mul_le_mul_of_nonneg_left hx_abs hd_nonneg
  have hdw_lt_pi : d * w < π :=
    (lt_div_iff₀ hw_pos).mp hd_threshold
  have hdw_half_lt : d * (w / 2) < π / 2 := by
    have hdiv : d * w / 2 < π / 2 :=
      div_lt_div_of_pos_right hdw_lt_pi zero_lt_two
    exact
      Eq.subst
        (motive := fun t : ℝ => t < π / 2)
        (mul_div_assoc d w 2).symm
        hdiv
  exact
    lt_of_le_of_lt
      (Eq.subst
        (motive := fun t : ℝ => t ≤ d * (w / 2))
        hmul_abs
        hmul_le)
      hdw_half_lt


end
end LFunctions
end Boundary
