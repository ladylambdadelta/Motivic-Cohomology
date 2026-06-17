import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.IsolatedZeros
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner

/-!
# Centered completed-zeta zeros and symmetries

This file owns the centered normalization formula, shifted-pole exclusion,
functional-equation symmetry, and critical-strip localization for centered
completed-zeta zeros.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter

theorem centeredCompletedRiemannZeta_eq (s : ℂ) :
    centeredCompletedRiemannZeta s =
      centeredCompletedRiemannZeta₀ s -
        1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) := by
  exact completedRiemannZeta_eq (1 / 2 + s)

/-- Excluding the negative shifted pole makes the left denominator nonzero. -/
theorem centeredShift_leftDenominator_ne_zero_of_ne_negHalf
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ)) :
    (1 / 2 : ℂ) + z ≠ 0 := by
  intro hzero
  have hz_eq : z = -(1 / 2 : ℂ) := by
    calc
      z = ((1 / 2 : ℂ) + z) - (1 / 2 : ℂ) := by ring
      _ = 0 - (1 / 2 : ℂ) := by
        exact congrArg (fun w : ℂ => w - (1 / 2 : ℂ)) hzero
      _ = -(1 / 2 : ℂ) := by ring
  exact hzneg hz_eq

/-- Excluding the positive shifted pole makes the right denominator nonzero. -/
theorem centeredShift_rightDenominator_ne_zero_of_ne_posHalf
    {z : ℂ}
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    1 - ((1 / 2 : ℂ) + z) ≠ 0 := by
  intro hzero
  have hz_eq : z = (1 / 2 : ℂ) := by
    have hz_sub : z - (1 / 2 : ℂ) = 0 := by
      calc
        z - (1 / 2 : ℂ) =
            -((1 : ℂ) - ((1 / 2 : ℂ) + z)) := by ring
        _ = -0 := by
          exact congrArg Neg.neg hzero
        _ = 0 := by
          exact neg_zero
    calc
      z = (z - (1 / 2 : ℂ)) + (1 / 2 : ℂ) := by ring
      _ = 0 + (1 / 2 : ℂ) := by
        exact congrArg (fun w : ℂ => w + (1 / 2 : ℂ)) hz_sub
      _ = (1 / 2 : ℂ) := by ring
  exact hzpos hz_eq

/-- Excluding both shifted poles makes the clearing denominator product nonzero. -/
theorem centeredShift_denominatorProduct_ne_zero_of_ne_shiftedPoles
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ))
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    ((1 / 2 : ℂ) + z) *
        (1 - ((1 / 2 : ℂ) + z)) ≠ 0 := by
  intro hmul
  match mul_eq_zero.mp hmul with
  | Or.inl hleft =>
      exact centeredShift_leftDenominator_ne_zero_of_ne_negHalf hzneg hleft
  | Or.inr hright =>
      exact centeredShift_rightDenominator_ne_zero_of_ne_posHalf hzpos hright

/-- The shifted denominator-clearing factor is analytic at every point. -/
theorem centeredShift_denominatorClearingFactor_analyticAt
    (z : ℂ) :
    AnalyticAt ℂ
      (fun w : ℂ =>
        ((1 / 2 : ℂ) + w) * (1 - ((1 / 2 : ℂ) + w))) z := by
  have hleft :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  have hright :
      AnalyticAt ℂ (fun w : ℂ => 1 - ((1 / 2 : ℂ) + w)) z :=
      analyticAt_const.sub (analyticAt_const.add analyticAt_id)
  exact hleft.mul hright

/-- Multiplying the left reciprocal pole by the cleared denominator leaves the right
denominator. -/
theorem denominatorProduct_mul_leftReciprocal
    {a b : ℂ} (ha : a ≠ 0) :
    a * b * (1 / a) = b := by
  calc
    a * b * (1 / a) = b * a * (1 / a) := by
      exact congrArg (fun x : ℂ => x * (1 / a)) (mul_comm a b)
    _ = b * (a * (1 / a)) := by
      exact mul_assoc b a (1 / a)
    _ = b * 1 := by
      exact congrArg (fun x : ℂ => b * x)
        (Eq.subst
          (motive := fun x : ℂ => a * x = 1)
          (inv_eq_one_div a)
          (mul_inv_cancel₀ ha))
    _ = b := by
      exact mul_one b

/-- Multiplying the right reciprocal pole by the cleared denominator leaves the left
denominator. -/
theorem denominatorProduct_mul_rightReciprocal
    {a b : ℂ} (hb : b ≠ 0) :
    a * b * (1 / b) = a := by
  calc
    a * b * (1 / b) = a * (b * (1 / b)) := by
      exact mul_assoc a b (1 / b)
    _ = a * 1 := by
      exact congrArg (fun x : ℂ => a * x)
        (Eq.subst
          (motive := fun x : ℂ => b * x = 1)
          (inv_eq_one_div b)
          (mul_inv_cancel₀ hb))
    _ = a := by
      exact mul_one a

/-- Clearing both reciprocal pole terms leaves subtraction by the sum of the two
denominators. -/
theorem denominatorProduct_mul_sub_twoReciprocals
    {a b E : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b * (E - 1 / a - 1 / b) =
      a * b * E - (a + b) := by
  calc
    a * b * (E - 1 / a - 1 / b) =
        a * b * (E - 1 / a) - a * b * (1 / b) := by
      exact mul_sub (a * b) (E - 1 / a) (1 / b)
    _ = (a * b * E - a * b * (1 / a)) - a * b * (1 / b) := by
      exact congrArg
        (fun x : ℂ => x - a * b * (1 / b))
        (mul_sub (a * b) E (1 / a))
    _ = (a * b * E - b) - a * b * (1 / b) := by
      exact congrArg
        (fun x : ℂ => (a * b * E - x) - a * b * (1 / b))
        (denominatorProduct_mul_leftReciprocal ha)
    _ = (a * b * E - b) - a := by
      exact congrArg
        (fun x : ℂ => (a * b * E - b) - x)
        (denominatorProduct_mul_rightReciprocal hb)
    _ = a * b * E - (a + b) := by
      calc
        (a * b * E - b) - a =
            a * b * E + -b + -a := by
          exact congrArg
            (fun x : ℂ => x + -a)
            (sub_eq_add_neg (a * b * E) b)
        _ = a * b * E + (-b + -a) := by
          exact add_assoc (a * b * E) (-b) (-a)
        _ = a * b * E + (-(b + a)) := by
          exact congrArg
            (fun x : ℂ => a * b * E + x)
            (neg_add b a).symm
        _ = a * b * E + (-(a + b)) := by
          exact congrArg
            (fun x : ℂ => a * b * E + (-x))
            (add_comm b a)
        _ = a * b * E - (a + b) := by
          exact (sub_eq_add_neg (a * b * E) (a + b)).symm

/-- The two shifted denominators sum to one. -/
theorem centeredShift_left_add_right_denominator
    (s : ℂ) :
    ((1 / 2 : ℂ) + s) + (1 - ((1 / 2 : ℂ) + s)) = 1 := by
  exact add_sub_cancel ((1 / 2 : ℂ) + s) 1

/-- Subtracting the sum of the two shifted denominators is subtraction by one. -/
theorem centeredShift_sub_denominatorSum_eq_sub_one
    (s E : ℂ) :
    ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) * E -
        (((1 / 2 : ℂ) + s) + (1 - ((1 / 2 : ℂ) + s))) =
      ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) * E - 1 := by
  exact congrArg
    (fun x : ℂ =>
      ((1 / 2 : ℂ) + s) * (1 - ((1 / 2 : ℂ) + s)) * E - x)
    (centeredShift_left_add_right_denominator s)

/-- Clearing the two shifted pole denominators identifies the centered completed
zeta normalization with the entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul
    {s : ℂ}
    (hs0 : (1 / 2 : ℂ) + s ≠ 0)
    (hs1 : 1 - ((1 / 2 : ℂ) + s) ≠ 0) :
    centeredCompletedRiemannZetaZeroCarrier s =
      ((1 / 2 : ℂ) + s) *
        (1 - ((1 / 2 : ℂ) + s)) *
          centeredCompletedRiemannZeta s := by
  let a : ℂ := (1 / 2 : ℂ) + s
  let b : ℂ := 1 - ((1 / 2 : ℂ) + s)
  let E : ℂ := centeredCompletedRiemannZeta₀ s
  have hcompleted :
      centeredCompletedRiemannZeta s =
        E - 1 / a - 1 / b := by
    exact centeredCompletedRiemannZeta_eq s
  have hcleared :
      a * b * centeredCompletedRiemannZeta s =
        a * b * E - (a + b) := by
    exact Eq.subst
      (motive := fun x : ℂ => a * b * x = a * b * E - (a + b))
      hcompleted.symm
      (denominatorProduct_mul_sub_twoReciprocals hs0 hs1)
  have hsum :
      a * b * E - (a + b) = a * b * E - 1 := by
    exact centeredShift_sub_denominatorSum_eq_sub_one s E
  calc
    centeredCompletedRiemannZetaZeroCarrier s =
        a * b * E - 1 := by
      rfl
    _ = a * b * centeredCompletedRiemannZeta s := by
      exact (hcleared.trans hsum).symm

/-- A non-pole zero of the centered completed zeta normalization is a zero of
the entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eq_zero_of_completed_zero
    {s : ℂ}
    (hs0 : (1 / 2 : ℂ) + s ≠ 0)
    (hs1 : 1 - ((1 / 2 : ℂ) + s) ≠ 0)
    (hz : centeredCompletedRiemannZeta s = 0) :
    centeredCompletedRiemannZetaZeroCarrier s = 0 := by
  calc
    centeredCompletedRiemannZetaZeroCarrier s =
        ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) *
            centeredCompletedRiemannZeta s := by
      exact centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hs0 hs1
    _ = ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) *
            0 := by
      exact congrArg
        (fun w : ℂ =>
          ((1 / 2 : ℂ) + s) *
            (1 - ((1 / 2 : ℂ) + s)) * w)
        hz
    _ = 0 := by
      exact mul_zero (((1 / 2 : ℂ) + s) * (1 - ((1 / 2 : ℂ) + s)))

/-- Away from the shifted poles, the centered completed zeta function is
analytic. The owner proof is the completed-zeta decomposition into an entire
part and two rational pole terms. -/
theorem centeredCompletedRiemannZeta_analyticAt_of_ne_shiftedPoles
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ))
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ centeredCompletedRiemannZeta z := by
  have hlinear :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  have hcenteredEntire :
      AnalyticAt ℂ centeredCompletedRiemannZeta₀ z := by
    exact centeredCompletedRiemannZeta₀_analyticAt z
  have hden_left :
      (1 / 2 : ℂ) + z ≠ 0 := by
    exact centeredShift_leftDenominator_ne_zero_of_ne_negHalf hzneg
  have hden_right :
      1 - ((1 / 2 : ℂ) + z) ≠ 0 := by
    exact centeredShift_rightDenominator_ne_zero_of_ne_posHalf hzpos
  have hleftPole :
      AnalyticAt ℂ (fun w : ℂ => 1 / ((1 / 2 : ℂ) + w)) z := by
    exact (analyticAt_const.div (analyticAt_const.add analyticAt_id) hden_left)
  have hrightPole :
      AnalyticAt ℂ (fun w : ℂ => 1 / (1 - ((1 / 2 : ℂ) + w))) z := by
    have hden :
        AnalyticAt ℂ (fun w : ℂ => 1 - ((1 / 2 : ℂ) + w)) z :=
      analyticAt_const.sub (analyticAt_const.add analyticAt_id)
    exact analyticAt_const.div hden hden_right
  have hformula :
      centeredCompletedRiemannZeta =
        (fun w : ℂ =>
          centeredCompletedRiemannZeta₀ w -
            1 / ((1 / 2 : ℂ) + w) -
              1 / (1 - ((1 / 2 : ℂ) + w))) := by
    funext w
    exact centeredCompletedRiemannZeta_eq w
  exact Eq.subst
    (motive := fun F : ℂ → ℂ => AnalyticAt ℂ F z)
    hformula.symm
    ((hcenteredEntire.sub hleftPole).sub hrightPole)

/-- If `(s - a)f(s)` tends to a nonzero limit on the punctured neighborhood of
`a`, then `f` is eventually nonzero on that punctured neighborhood. -/
theorem eventually_ne_zero_of_tendsto_sub_mul_ne_zero
    {f : ℂ → ℂ} {a c : ℂ}
    (hc : c ≠ 0)
    (hlim : Tendsto (fun s : ℂ => (s - a) * f s) (𝓝[≠] a) (𝓝 c)) :
    ∀ᶠ s in 𝓝 a, s ≠ a → f s ≠ 0 := by
  have hprod :
      ∀ᶠ s in 𝓝[≠] a, (s - a) * f s ≠ 0 :=
    hlim.eventually_ne hc
  have hprod' :
      ∀ᶠ s in 𝓝 a, s ≠ a → (s - a) * f s ≠ 0 := by
    exact (eventually_nhdsWithin_iff.mp hprod)
  exact hprod'.mono
    (fun s hs hs_ne hf_zero =>
      hs hs_ne
        (by
          calc
            (s - a) * f s = (s - a) * 0 := by
              exact congrArg (fun t : ℂ => (s - a) * t) hf_zero
            _ = 0 := by
              exact mul_zero (s - a)))

/-- The completed zeta normalization has residue `-1` at `0`. -/
theorem completedRiemannZeta_residue_zero :
    Tendsto
      (fun s : ℂ => s * completedRiemannZeta s)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-(1 : ℂ))) := by
  change
    Tendsto
      (fun s : ℂ => s * HurwitzZeta.completedHurwitzZetaEven (0 : UnitAddCircle) s)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-(1 : ℂ)))
  have hresidue :
      Tendsto
        (fun s : ℂ => s * HurwitzZeta.completedHurwitzZetaEven (0 : UnitAddCircle) s)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (if (0 : UnitAddCircle) = 0 then -(1 : ℂ) else 0)) :=
    HurwitzZeta.completedHurwitzZetaEven_residue_zero (a := (0 : UnitAddCircle))
  have hvalue :
      (if (0 : UnitAddCircle) = 0 then -(1 : ℂ) else 0) = -(1 : ℂ) :=
    if_pos rfl
  exact Eq.subst
    (motive := fun c : ℂ =>
      Tendsto
        (fun s : ℂ => s * HurwitzZeta.completedHurwitzZetaEven (0 : UnitAddCircle) s)
        (𝓝[≠] (0 : ℂ))
        (𝓝 c))
    hvalue
    hresidue

/-- Adding `1/2` sends the punctured neighborhood of `-1/2` to the punctured
neighborhood of `0`. -/
theorem centeredShift_tendsto_punctured_negHalf_to_zero :
    Tendsto
      (fun w : ℂ => (1 / 2 : ℂ) + w)
      (𝓝[≠] (-(1 / 2 : ℂ)))
      (𝓝[≠] (0 : ℂ)) := by
  have hraw :
      Tendsto
        (Homeomorph.addLeft (1 / 2 : ℂ))
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝[≠] ((Homeomorph.addLeft (1 / 2 : ℂ)) (-(1 / 2 : ℂ)))) := by
    exact le_of_eq
      ((Homeomorph.addLeft (1 / 2 : ℂ)).map_punctured_nhds_eq (-(1 / 2 : ℂ)))
  have hend :
      ((Homeomorph.addLeft (1 / 2 : ℂ)) (-(1 / 2 : ℂ))) = 0 := by
    change (1 / 2 : ℂ) + (-(1 / 2 : ℂ)) = 0
    exact add_neg_cancel (1 / 2 : ℂ)
  exact Eq.subst
    (motive := fun x : ℂ =>
      Tendsto
        (Homeomorph.addLeft (1 / 2 : ℂ))
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝[≠] x))
    hend
    hraw

/-- Adding `1/2` sends the punctured neighborhood of `1/2` to the punctured
neighborhood of `1`. -/
theorem centeredShift_tendsto_punctured_posHalf_to_one :
    Tendsto
      (fun w : ℂ => (1 / 2 : ℂ) + w)
      (𝓝[≠] ((1 / 2 : ℂ)))
      (𝓝[≠] (1 : ℂ)) := by
  have hmap_half :
      Tendsto
        (Homeomorph.addLeft (1 / 2 : ℂ))
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝[≠] ((Homeomorph.addLeft (1 / 2 : ℂ)) ((1 / 2 : ℂ)))) := by
    exact le_of_eq
      ((Homeomorph.addLeft (1 / 2 : ℂ)).map_punctured_nhds_eq ((1 / 2 : ℂ)))
  have hhalf :
      ((Homeomorph.addLeft (1 / 2 : ℂ)) ((1 / 2 : ℂ))) = 1 := by
    change (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1
    norm_num
  exact Eq.subst
    (motive := fun x : ℂ =>
      Tendsto
        (Homeomorph.addLeft (1 / 2 : ℂ))
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝[≠] x))
    hhalf
    hmap_half

/-- The centered completed zeta function is nonzero in a punctured neighborhood
of the negative shifted pole. -/
theorem centeredCompletedRiemannZeta_eventually_ne_zero_punctured_negHalf :
    ∀ᶠ w in 𝓝 (-(1 / 2 : ℂ)),
      w ≠ -(1 / 2 : ℂ) → centeredCompletedRiemannZeta w ≠ 0 := by
  have hmap :
      Tendsto
        (fun w : ℂ => (1 / 2 : ℂ) + w)
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝[≠] (0 : ℂ)) := by
    exact centeredShift_tendsto_punctured_negHalf_to_zero
  have hlim :
      Tendsto
        (fun w : ℂ =>
          ((1 / 2 : ℂ) + w) *
            completedRiemannZeta ((1 / 2 : ℂ) + w))
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝 (-(1 : ℂ))) :=
    completedRiemannZeta_residue_zero.comp hmap
  have hcentered :
      Tendsto
        (fun w : ℂ =>
          (w - (-(1 / 2 : ℂ))) * centeredCompletedRiemannZeta w)
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝 (-(1 : ℂ))) := by
    exact hlim.congr'
      (Eventually.of_forall
        (fun w : ℂ => by
          unfold centeredCompletedRiemannZeta
          congr 1
          ring))
  exact eventually_ne_zero_of_tendsto_sub_mul_ne_zero
    (f := centeredCompletedRiemannZeta)
    (a := -(1 / 2 : ℂ))
    (c := -(1 : ℂ))
    (by norm_num)
    hcentered

/-- The centered completed zeta function is nonzero in a punctured neighborhood
of the positive shifted pole. -/
theorem centeredCompletedRiemannZeta_eventually_ne_zero_punctured_posHalf :
    ∀ᶠ w in 𝓝 ((1 / 2 : ℂ)),
      w ≠ (1 / 2 : ℂ) → centeredCompletedRiemannZeta w ≠ 0 := by
  have hmap :
      Tendsto
        (fun w : ℂ => (1 / 2 : ℂ) + w)
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝[≠] (1 : ℂ)) := by
    exact centeredShift_tendsto_punctured_posHalf_to_one
  have hlim :
      Tendsto
        (fun w : ℂ =>
          (((1 / 2 : ℂ) + w) - 1) *
            completedRiemannZeta ((1 / 2 : ℂ) + w))
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝 (1 : ℂ)) :=
    completedRiemannZeta_residue_one.comp hmap
  have hcentered :
      Tendsto
        (fun w : ℂ =>
          (w - (1 / 2 : ℂ)) * centeredCompletedRiemannZeta w)
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝 (1 : ℂ)) := by
    exact hlim.congr'
      (Eventually.of_forall
        (fun w : ℂ => by
          unfold centeredCompletedRiemannZeta
          congr 1
          ring))
  exact eventually_ne_zero_of_tendsto_sub_mul_ne_zero
    (f := centeredCompletedRiemannZeta)
    (a := (1 / 2 : ℂ))
    (c := (1 : ℂ))
    one_ne_zero
    hcentered

theorem centeredCompletedRiemannZeta_neg (s : ℂ) :
    centeredCompletedRiemannZeta (-s) = centeredCompletedRiemannZeta s := by
  have hsub : (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s := by
    show (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s
    exact (sub_add_eq_sub_sub 1 (1 / 2) s).symm
  have hsymm :
      completedRiemannZeta (1 / 2 - s) = completedRiemannZeta (1 - (1 / 2 + s)) := by
    exact congrArg completedRiemannZeta hsub.symm
  exact hsymm.trans (completedRiemannZeta_one_sub (1 / 2 + s))

theorem centeredCompletedRiemannZeta₀_neg (s : ℂ) :
    centeredCompletedRiemannZeta₀ (-s) = centeredCompletedRiemannZeta₀ s := by
  have hsub : (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s := by
    show (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s
    exact (sub_add_eq_sub_sub 1 (1 / 2) s).symm
  have hsymm :
      completedRiemannZeta₀ (1 / 2 - s) = completedRiemannZeta₀ (1 - (1 / 2 + s)) := by
    exact congrArg completedRiemannZeta₀ hsub.symm
  exact hsymm.trans (completedRiemannZeta₀_one_sub (1 / 2 + s))

theorem centeredCompletedRiemannZeta_correction_symm (s : ℂ) :
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
      1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
  have h1 : (1 / 2 : ℂ) + (-s) = (1 / 2 : ℂ) - s := by
    exact sub_eq_add_neg (1 / 2) s
  have h2 : (1 : ℂ) - ((1 / 2 : ℂ) - s) = (1 / 2 : ℂ) + s := by
    show (1 : ℂ) - ((1 / 2 : ℂ) - s) = (1 / 2 : ℂ) + s
    exact sub_sub_eq_add_sub 1 (1 / 2) s
  have h3 : (1 : ℂ) - (1 / 2 + s) = (1 / 2 : ℂ) - s := by
    show (1 : ℂ) - (1 / 2 + s) = (1 / 2 : ℂ) - s
    exact (sub_add_eq_sub_sub 1 (1 / 2) s).symm
  calc
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
        1 / ((1 / 2 : ℂ) - s) + 1 / (1 - ((1 / 2 : ℂ) - s)) := by
      exact congrArg (fun x : ℂ => 1 / x + 1 / (1 - x)) h1
    _ = 1 / ((1 / 2 : ℂ) - s) + 1 / (1 / 2 + s) := by
      exact congrArg (fun x : ℂ => 1 / ((1 / 2 : ℂ) - s) + x)
        (congrArg (fun x : ℂ => 1 / x) h2)
    _ = 1 / (1 / 2 + s) + 1 / ((1 / 2 : ℂ) - s) := by
      exact add_comm (1 / ((1 / 2 : ℂ) - s)) (1 / (1 / 2 + s))
    _ = 1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
      exact congrArg (fun x : ℂ => 1 / (1 / 2 + s) + x)
        (congrArg (fun x : ℂ => 1 / x) h3.symm)

/-- Completed zeta has no zeros in the half-plane to the right of `1`. -/
theorem completedRiemannZeta_ne_zero_of_one_lt_re
    (s : ℂ)
    (hsre : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  intro hs
  have hs0 : s ≠ 0 := by
    intro hs_zero
    have hre_zero : s.re = 0 := by
      exact congrArg Complex.re hs_zero
    have hone_lt_zero : (1 : ℝ) < 0 :=
      Eq.subst
        (motive := fun x : ℝ => 1 < x)
        hre_zero
        hsre
    exact (not_lt_of_ge zero_le_one) hone_lt_zero
  have hζ_eq :
      riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  have hζ_zero : riemannZeta s = 0 := by
    calc
      riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s := hζ_eq
      _ = 0 / Complex.Gammaℝ s := by
        exact congrArg (fun x : ℂ => x / Complex.Gammaℝ s) hs
      _ = 0 := by
        exact zero_div (Complex.Gammaℝ s)
  exact riemannZeta_ne_zero_of_one_lt_re hsre hζ_zero

/-- Completed zeta has no zeros in the left half-plane. -/
theorem completedRiemannZeta_ne_zero_of_re_lt_zero
    (s : ℂ)
    (hsre : s.re < 0) :
    completedRiemannZeta s ≠ 0 := by
  intro hs
  have hright_re :
      1 < ((1 : ℂ) - s).re := by
    have hre :
        ((1 : ℂ) - s).re = 1 - s.re := by
      exact Complex.sub_re (1 : ℂ) s
    have hlt : 1 < 1 - s.re := by
      have hsum : s.re + 1 < 0 + 1 :=
        add_lt_add_right hsre 1
      have hsum_one : s.re + 1 < 1 :=
        Eq.subst
          (motive := fun x : ℝ => s.re + 1 < x)
          (zero_add (1 : ℝ))
          hsum
      exact lt_sub_iff_add_lt'.2 hsum_one
    exact Eq.subst
      (motive := fun x : ℝ => 1 < x)
      hre.symm
      hlt
  have hright_ne :
      completedRiemannZeta ((1 : ℂ) - s) ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_lt_re ((1 : ℂ) - s) hright_re
  have hsymm :
      completedRiemannZeta ((1 : ℂ) - s) =
        completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  exact hright_ne (hsymm.trans hs)

/-- Completed-zeta zeros lie in the ordinary critical strip.

This is the standard unconditional critical-strip theorem for zeros of the
completed Riemann zeta normalization. -/
theorem completedRiemannZeta_zero_re_mem_criticalStrip
    (s : ℂ)
    (hs : completedRiemannZeta s = 0) :
    0 ≤ s.re ∧ s.re ≤ (1 : ℝ) := by
  have hnot_left : ¬ s.re < 0 := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_re_lt_zero s hsre hs
  have hnot_right : ¬ (1 : ℝ) < s.re := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_one_lt_re s hsre hs
  exact ⟨le_of_not_gt hnot_left, le_of_not_gt hnot_right⟩

/-- The real coordinate of the uncentered argument is the centered real
coordinate shifted by `1/2`. -/
theorem centeredCompletedRiemannZeta_uncenter_re
    (s : ℂ) :
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re := by
  calc
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℂ).re + s.re := by
      exact Complex.add_re (1 / 2 : ℂ) s
    _ = (1 / 2 : ℝ) + s.re := by
      have hhalf_re : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by
        norm_num
      exact congrArg (fun x : ℝ => x + s.re) hhalf_re

/-- If the uncentered coordinate lies in `[0,1]`, the centered coordinate lies
in `[-1/2,1/2]`. -/
theorem centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    {x : ℝ}
    (hleft : 0 ≤ (1 / 2 : ℝ) + x)
    (hright : (1 / 2 : ℝ) + x ≤ 1) :
    -(1 / 2 : ℝ) ≤ x ∧ x ≤ (1 / 2 : ℝ) := by
  have hleft' :
      -(1 / 2 : ℝ) ≤ x :=
    (neg_le_iff_add_nonneg).2
      (Eq.subst
        (motive := fun y : ℝ => 0 ≤ y)
        (add_comm (1 / 2 : ℝ) x)
        hleft)
  have hright_comm :
      x + (1 / 2 : ℝ) ≤ 1 :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ 1)
      (add_comm (1 / 2 : ℝ) x)
      hright
  have hright_sub :
      x ≤ (1 : ℝ) - (1 / 2 : ℝ) :=
    (le_sub_iff_add_le).2 hright_comm
  have hhalf :
      (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) :=
    sub_half (1 : ℝ)
  have hright' :
      x ≤ (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun y : ℝ => x ≤ y)
      hhalf
      hright_sub
  exact ⟨hleft', hright'⟩

/-- Centered completed-zeta zeros lie in the centered critical strip.

This is the standard unconditional critical-strip theorem for nontrivial zeta
zeros, expressed in the centered completed-zeta normalization used by the
zero-side explicit formula. -/
theorem centeredCompletedRiemannZeta_zero_re_mem_centeredCriticalStrip
    (s : ℂ)
    (hs : centeredCompletedRiemannZeta s = 0) :
    -(1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ (1 / 2 : ℝ) := by
  have huncentered_zero :
      completedRiemannZeta ((1 / 2 : ℂ) + s) = 0 := by
    exact hs
  have hstrip :
      0 ≤ ((1 / 2 : ℂ) + s).re ∧
        ((1 / 2 : ℂ) + s).re ≤ (1 : ℝ) :=
    completedRiemannZeta_zero_re_mem_criticalStrip
      ((1 / 2 : ℂ) + s)
      huncentered_zero
  have hre :
      ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re :=
    centeredCompletedRiemannZeta_uncenter_re s
  have hleft :
      0 ≤ (1 / 2 : ℝ) + s.re :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hre
      hstrip.1
  have hright :
      (1 / 2 : ℝ) + s.re ≤ 1 :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ (1 : ℝ))
      hre
      hstrip.2
  exact centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    hleft
    hright

end

end LFunctions
end Boundary
