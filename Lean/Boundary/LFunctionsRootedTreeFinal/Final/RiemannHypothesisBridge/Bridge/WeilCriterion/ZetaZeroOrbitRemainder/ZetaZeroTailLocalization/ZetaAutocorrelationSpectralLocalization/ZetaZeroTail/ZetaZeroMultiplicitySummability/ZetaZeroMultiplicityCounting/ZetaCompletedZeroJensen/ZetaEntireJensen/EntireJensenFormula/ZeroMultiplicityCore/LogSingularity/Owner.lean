import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.BoundaryArc.Owner

/-!
# Logarithmic singularity integrability core

This owner layer was split from `ZeroMultiplicityCore.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- The function `x - x log x` is continuous on the closed unit interval. -/
theorem real_continuousOn_x_sub_x_mul_log_on_unitIcc :
    ContinuousOn (fun x : ℝ => x - x * Real.log x) [[(0 : ℝ), 1]] := by
  have hcont : ContinuousOn (fun x : ℝ => x - x * Real.log x) (Set.Icc (0 : ℝ) 1) :=
    (continuous_id.sub Real.continuous_mul_log).continuousOn
  exact Eq.subst
    (motive := fun s : Set ℝ =>
      ContinuousOn (fun x : ℝ => x - x * Real.log x) s)
    (Set.uIcc_of_le zero_le_one).symm
    hcont

/-- The logarithmic singularity `-log` is interval-integrable on `[0,1]`. -/
theorem real_intervalIntegrable_neg_log_unitInterval :
    IntervalIntegrable (fun x : ℝ => -Real.log x) MeasureTheory.volume 0 1 := by
  have hcont := real_continuousOn_x_sub_x_mul_log_on_unitIcc
  have hderiv :
      ∀ x ∈ Set.Ioo ((0 : ℝ) ⊓ 1) ((0 : ℝ) ⊔ 1),
        HasDerivAt (fun x : ℝ => x - x * Real.log x) (-Real.log x) x := by
    intro x hx
    have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
      have hleft : (0 : ℝ) ⊓ 1 = 0 :=
        min_eq_left zero_le_one
      have hright : (0 : ℝ) ⊔ 1 = 1 :=
        max_eq_right zero_le_one
      have hx_left : x ∈ Set.Ioo (0 : ℝ) ((0 : ℝ) ⊔ 1) :=
        Eq.subst
          (motive := fun y : ℝ => x ∈ Set.Ioo y ((0 : ℝ) ⊔ 1))
          hleft
          hx
      exact
        Eq.subst
          (motive := fun y : ℝ => x ∈ Set.Ioo (0 : ℝ) y)
          hright
          hx_left
    exact real_hasDerivAt_x_sub_x_mul_log_unitIoo x hx01
  have hnonneg : ∀ x ∈ Set.Ioo ((0 : ℝ) ⊓ 1) ((0 : ℝ) ⊔ 1), 0 ≤ -Real.log x := by
    intro x hx
    have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
      have hleft : (0 : ℝ) ⊓ 1 = 0 :=
        min_eq_left zero_le_one
      have hright : (0 : ℝ) ⊔ 1 = 1 :=
        max_eq_right zero_le_one
      have hx_left : x ∈ Set.Ioo (0 : ℝ) ((0 : ℝ) ⊔ 1) :=
        Eq.subst
          (motive := fun y : ℝ => x ∈ Set.Ioo y ((0 : ℝ) ⊔ 1))
          hleft
          hx
      exact
        Eq.subst
          (motive := fun y : ℝ => x ∈ Set.Ioo (0 : ℝ) y)
          hright
          hx_left
    have hx0 : 0 < x := (Set.mem_Ioo.mp hx01).1
    have hx1 : x ≤ 1 := (Set.mem_Ioo.mp hx01).2.le
    exact neg_nonneg.mpr (Real.log_nonpos hx0.le hx1)
  exact intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont hderiv hnonneg

/-- The real logarithm is interval-integrable on `[0,1]`. -/
theorem real_intervalIntegrable_log_unitInterval :
    IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 1 := by
  have hneg :
      IntervalIntegrable (fun x : ℝ => -(-Real.log x)) MeasureTheory.volume 0 1 := by
    exact real_intervalIntegrable_neg_log_unitInterval.neg
  exact
    IntervalIntegrable.congr hneg
      (Filter.Eventually.of_forall
        (fun x => neg_neg (Real.log x)))

/-- The unit-interval logarithm remains interval-integrable after scaling the
variable by a positive constant. -/
theorem real_intervalIntegrable_log_scaled_unitInterval
    {t : ℝ}
    (hpos : 0 < t) :
    IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹)) MeasureTheory.volume 0 t := by
  have hcomp :=
    IntervalIntegrable.comp_mul_right real_intervalIntegrable_log_unitInterval (t⁻¹)
  have hleft : (0 : ℝ) / t⁻¹ = 0 := zero_div t⁻¹
  have hright : (1 : ℝ) / t⁻¹ = t := by
    calc
      (1 : ℝ) / t⁻¹ = 1 * (t⁻¹)⁻¹ := div_eq_mul_inv 1 t⁻¹
      _ = (t⁻¹)⁻¹ := one_mul (t⁻¹)⁻¹
      _ = t := inv_inv t
  have hcomp_left :
      IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹)) MeasureTheory.volume
        0 (1 / t⁻¹) :=
    Eq.subst
      (motive := fun left : ℝ =>
        IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹)) MeasureTheory.volume
          left (1 / t⁻¹))
      hleft
      hcomp
  exact Eq.subst
    (motive := fun right : ℝ =>
      IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹)) MeasureTheory.volume
        0 right)
    hright
    hcomp_left

/-- The scaled logarithm identity used in the Jensen interval transport. -/
theorem real_log_scaled_mul_inv_add
    {x t : ℝ}
    (hx0 : x ≠ 0)
    (ht0 : t ≠ 0) :
    Real.log (x * t⁻¹) + Real.log t = Real.log x := by
  have hxt : (x * t⁻¹) * t = x := by
    calc
      (x * t⁻¹) * t = x * (t⁻¹ * t) :=
        mul_assoc x t⁻¹ t
      _ = x * 1 := by
        exact congrArg (fun y : ℝ => x * y) (inv_mul_cancel₀ ht0)
      _ = x := mul_one x
  calc
    Real.log (x * t⁻¹) + Real.log t = Real.log ((x * t⁻¹) * t) := by
      symm
      exact Real.log_mul (mul_ne_zero hx0 (inv_ne_zero ht0)) ht0
    _ = Real.log x := by
      exact congrArg Real.log hxt

/-- The real logarithm is interval-integrable on a compact interval starting at
`0`. -/
theorem real_intervalIntegrable_log_Icc {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 t := by
  match lt_or_eq_of_le ht with
  | Or.inl hpos =>
    have hscaled :
        IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹)) MeasureTheory.volume 0 t := by
      exact real_intervalIntegrable_log_scaled_unitInterval hpos
    have hconst : IntervalIntegrable (fun _ : ℝ => Real.log t) MeasureTheory.volume 0 t :=
      intervalIntegrable_const
    have hsum :
        IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹) + Real.log t)
          MeasureTheory.volume 0 t :=
      hscaled.add hconst
    have hsumOn :
        IntegrableOn (fun x : ℝ => Real.log (x * t⁻¹) + Real.log t)
          (Set.Ioc 0 t) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hpos.le).mp hsum
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpos.le).mpr
      (IntegrableOn.congr_fun hsumOn
        (by
          intro x hx
          have hx0 : x ≠ 0 := (mem_Ioc.mp hx).1.ne'
          have ht0 : t ≠ 0 := hpos.ne'
          exact real_log_scaled_mul_inv_add hx0 ht0)
        measurableSet_Ioc)
  | Or.inr ht_eq =>
    have hzero :
        IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 0 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le le_rfl).2
        (by
          have hIoc_empty : Set.Ioc (0 : ℝ) 0 = ∅ :=
            Ioc_eq_empty_of_le le_rfl
          exact Eq.subst
            (motive := fun s : Set ℝ =>
              IntegrableOn (fun x : ℝ => Real.log x) s MeasureTheory.volume)
            hIoc_empty.symm
            integrableOn_empty)
    have htransport :
        IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume
          0 t =
        IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume
          0 0 := by
      exact congrArg
        (fun right : ℝ =>
          IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume
            0 right)
        ht_eq.symm
    exact Eq.mpr htransport hzero

/-- The absolute value on the left side of `c` is `c - x`. -/
theorem real_abs_sub_const_of_le
    {x c : ℝ}
    (hx : x ≤ c) :
    |x - c| = c - x := by
  have hnonpos : x - c ≤ 0 := by
    exact sub_nonpos.mpr hx
  calc
    |x - c| = -(x - c) := abs_of_nonpos hnonpos
    _ = c - x := neg_sub x c

/-- The absolute value on the right side of `c` is `x - c`. -/
theorem real_abs_sub_const_of_ge
    {x c : ℝ}
    (hx : c ≤ x) :
    |x - c| = x - c := by
  have hnonneg : 0 ≤ x - c := by
    exact sub_nonneg.mpr hx
  exact abs_of_nonneg hnonneg

/-- The left-translate logarithm is interval-integrable on the left half of a
compact interval. -/
theorem intervalIntegrable_log_sub_left_on_compact
    {a c : ℝ}
    (hac : a ≤ c) :
    IntervalIntegrable (fun x : ℝ => Real.log (c - x)) MeasureTheory.volume a c := by
  have hbase :
      IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 (c - a) := by
    exact real_intervalIntegrable_log_Icc (sub_nonneg.mpr hac)
  have hcomp :
      IntervalIntegrable (fun x : ℝ => Real.log (c - x)) MeasureTheory.volume
        (c - 0) (c - (c - a)) :=
    IntervalIntegrable.comp_sub_left hbase c
  have hleft : c - (c - a) = a := sub_sub_cancel c a
  have hright : c - 0 = c := sub_zero c
  have hcomp_left :
      IntervalIntegrable (fun x : ℝ => Real.log (c - x)) MeasureTheory.volume
        a (c - 0) :=
    Eq.subst
      (motive := fun left : ℝ =>
        IntervalIntegrable (fun x : ℝ => Real.log (c - x)) MeasureTheory.volume
          left (c - 0))
      hleft
      hcomp.symm
  exact Eq.subst
    (motive := fun right : ℝ =>
      IntervalIntegrable (fun x : ℝ => Real.log (c - x)) MeasureTheory.volume
        a right)
    hright
    hcomp_left

/-- The right-translate logarithm is interval-integrable on the right half of a
compact interval. -/
theorem intervalIntegrable_log_sub_right_on_compact
    {c b : ℝ}
    (hcb : c ≤ b) :
    IntervalIntegrable (fun x : ℝ => Real.log (x - c)) MeasureTheory.volume c b := by
  have hbase :
      IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 (b - c) := by
    exact real_intervalIntegrable_log_Icc (sub_nonneg.mpr hcb)
  have hcomp :
      IntervalIntegrable (fun x : ℝ => Real.log (x - c)) MeasureTheory.volume
        (0 + c) (b - c + c) :=
    IntervalIntegrable.comp_sub_right hbase c
  have hleft : 0 + c = c := zero_add c
  have hright : b - c + c = b := sub_add_cancel b c
  have hcomp_left :
      IntervalIntegrable (fun x : ℝ => Real.log (x - c)) MeasureTheory.volume
        c (b - c + c) :=
    Eq.subst
      (motive := fun left : ℝ =>
        IntervalIntegrable (fun x : ℝ => Real.log (x - c)) MeasureTheory.volume
          left (b - c + c))
      hleft
      hcomp
  exact Eq.subst
    (motive := fun right : ℝ =>
      IntervalIntegrable (fun x : ℝ => Real.log (x - c)) MeasureTheory.volume
        c right)
    hright
    hcomp_left

/-- On the left side of `c`, `log |x-c|` agrees with `log (c-x)`. -/
theorem real_log_abs_sub_const_eq_log_sub_left
    {x c : ℝ}
    (hx : x ≤ c) :
    Real.log |x - c| = Real.log (c - x) := by
  exact congrArg Real.log (real_abs_sub_const_of_le hx)

/-- On the right side of `c`, `log |x-c|` agrees with `log (x-c)`. -/
theorem real_log_abs_sub_const_eq_log_sub_right
    {x c : ℝ}
    (hx : c ≤ x) :
    Real.log |x - c| = Real.log (x - c) := by
  exact congrArg Real.log (real_abs_sub_const_of_ge hx)

/-- The translated absolute-distance logarithm is interval-integrable on a
compact interval. This is the one-dimensional singularity model used in the
Jensen local gluing theorem. -/
theorem intervalIntegrable_log_abs_sub_const_on_compact
    {a b c : ℝ}
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    IntervalIntegrable (fun x : ℝ => Real.log |x - c|) MeasureTheory.volume a b := by
  have hab : a ≤ b := hac.trans hcb
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (by
      have hsplit :
          IntegrableOn (fun x : ℝ => Real.log |x - c|) (Set.Ioc a c ∪ Set.Ioc c b)
            MeasureTheory.volume := by
        have hleft :
            IntervalIntegrable (fun x : ℝ => Real.log (c - x))
              MeasureTheory.volume a c := by
          exact intervalIntegrable_log_sub_left_on_compact hac
        have hleftOn :
            IntegrableOn (fun x : ℝ => Real.log (c - x)) (Set.Ioc a c)
              MeasureTheory.volume := by
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mp hleft
        have hleftAbs :
            IntegrableOn (fun x : ℝ => Real.log |x - c|) (Set.Ioc a c)
              MeasureTheory.volume :=
          hleftOn.congr_fun
            (by
              intro x hx
              have hx' : x ≤ c := (mem_Ioc.mp hx).2
              exact (real_log_abs_sub_const_eq_log_sub_left hx').symm)
            measurableSet_Ioc
        have hright :
            IntervalIntegrable (fun x : ℝ => Real.log (x - c))
              MeasureTheory.volume c b := by
          exact intervalIntegrable_log_sub_right_on_compact hcb
        have hrightOn :
            IntegrableOn (fun x : ℝ => Real.log (x - c)) (Set.Ioc c b)
              MeasureTheory.volume := by
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcb).mp hright
        have hrightAbs :
            IntegrableOn (fun x : ℝ => Real.log |x - c|) (Set.Ioc c b)
              MeasureTheory.volume :=
          hrightOn.congr_fun
            (by
              intro x hx
              have hx' : c ≤ x := le_of_lt (mem_Ioc.mp hx).1
              exact (real_log_abs_sub_const_eq_log_sub_right hx').symm)
            measurableSet_Ioc
        exact integrableOn_union.mpr ⟨hleftAbs, hrightAbs⟩
      have hIoc_union : Set.Ioc a b = Set.Ioc a c ∪ Set.Ioc c b :=
        (Ioc_union_Ioc_eq_Ioc hac hcb).symm
      exact Eq.subst
        (motive := fun s : Set ℝ =>
          IntegrableOn (fun x : ℝ => Real.log |x - c|) s MeasureTheory.volume)
        hIoc_union.symm
        hsplit)

/-- A real scalar multiple of the translated logarithmic singularity is
interval-integrable on every compact interval containing the singular point. -/
theorem intervalIntegrable_const_mul_log_abs_sub_const_on_compact
    {a b c : ℝ}
    (A : ℝ)
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    IntervalIntegrable
      (fun x : ℝ => A * Real.log |x - c|)
      MeasureTheory.volume a b := by
  exact
    (intervalIntegrable_log_abs_sub_const_on_compact hac hcb).const_mul A

/-- The natural-multiplicity logarithmic term in a local Jensen model is
interval-integrable on every compact interval containing the singular point. -/
theorem intervalIntegrable_nat_mul_log_abs_sub_const_on_compact
    {a b c : ℝ}
    (n : ℕ)
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    IntervalIntegrable
      (fun x : ℝ => (n : ℝ) * Real.log |x - c|)
      MeasureTheory.volume a b := by
  exact
    intervalIntegrable_const_mul_log_abs_sub_const_on_compact
      (n : ℝ) hac hcb

/-- Adding an already interval-integrable remainder to a logarithmic
singularity preserves interval-integrability on the compact model interval. -/
theorem intervalIntegrable_log_singularity_model_on_compact
    {a b c : ℝ}
    (n : ℕ)
    (g : ℝ → ℝ)
    (hac : a ≤ c)
    (hcb : c ≤ b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    IntervalIntegrable
      (fun x : ℝ => (n : ℝ) * Real.log |x - c| + g x)
      MeasureTheory.volume a b := by
  exact
    (intervalIntegrable_nat_mul_log_abs_sub_const_on_compact n hac hcb).add hg

/-- Interval-integrability restricts to a smaller unordered compact interval
whose endpoints both lie in the original unordered compact interval. -/
theorem intervalIntegrable_mono_of_uIcc_endpoint_mem
    {f : ℝ → ℝ}
    {a b u v : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hu : u ∈ [[a, b]])
    (hv : v ∈ [[a, b]]) :
    IntervalIntegrable f MeasureTheory.volume u v := by
  exact hf.mono_set (Set.uIcc_subset_uIcc hu hv)

/-- A punctured-neighborhood equality can be shrunk to a compact subinterval
on which the two functions are equal almost everywhere.

This is the topological/null-set extraction behind punctured logarithmic local
models: the equality holds on a deleted neighborhood of `c`, and the missing
center point is null for Lebesgue measure. -/
theorem eventuallyEq_punctured_nhdsWithin_has_subinterval_aeEq
    {f g : ℝ → ℝ}
    {c u v : ℝ}
    (huc : u < c)
    (hcv : c < v)
    (hfg : ∀ᶠ θ in 𝓝[≠] c, f θ = g θ) :
    ∃ u' v' : ℝ,
      u < u' ∧ u' < c ∧ c < v' ∧ v' < v ∧
      g =ᵐ[MeasureTheory.volume.restrict (Ι u' v')] f := by
  have hfg' : {θ : ℝ | θ ≠ c → f θ = g θ} ∈ 𝓝 c := by
    have hfg₀ : ∀ᶠ θ in 𝓝 c, θ ≠ c → f θ = g θ := by
      have hfgWithin :
          ∀ᶠ θ in 𝓝 c, θ ∈ ({c}ᶜ : Set ℝ) → f θ = g θ := by
        exact Filter.eventually_inf_principal.mp hfg
      exact
        hfgWithin.mono
          (fun θ hθ hθ_ne => hθ hθ_ne)
    exact hfg₀
  match mem_nhds_iff_exists_Ioo_subset.mp hfg' with
  | ⟨l, r, hc_lr, hsub_lr⟩ =>
      let leftBound : ℝ := max u l
      let rightBound : ℝ := min v r
      let u' : ℝ := (leftBound + c) / 2
      let v' : ℝ := (c + rightBound) / 2
      have hleft_lt_c : leftBound < c := max_lt huc hc_lr.1
      have hc_lt_right : c < rightBound := lt_min hcv hc_lr.2
      have hu_u' : u < u' := by
        show u < (max u l + c) / 2
        have hu_left : u ≤ max u l := le_max_left u l
        exact (lt_div_iff₀ zero_lt_two).mpr
          (calc
            u * 2 = u + u := mul_two u
            _ ≤ u + max u l := add_le_add_left hu_left u
            _ = max u l + u := add_comm u (max u l)
            _ < max u l + c := add_lt_add_left huc (max u l))
      have hu'_c : u' < c := by
        show (leftBound + c) / 2 < c
        exact (div_lt_iff₀ zero_lt_two).mpr
          (calc
            leftBound + c < c + c := add_lt_add_right hleft_lt_c c
            _ = c * 2 := (mul_two c).symm)
      have hc_v' : c < v' := by
        show c < (c + rightBound) / 2
        exact (lt_div_iff₀ zero_lt_two).mpr
          (calc
            c * 2 = c + c := mul_two c
            _ < c + rightBound := add_lt_add_left hc_lt_right c)
      have hv'_v : v' < v := by
        show (c + min v r) / 2 < v
        have hright_v : min v r ≤ v := min_le_left v r
        exact (div_lt_iff₀ zero_lt_two).mpr
          (calc
            c + min v r < v + min v r := add_lt_add_right hcv (min v r)
            _ ≤ v + v := add_le_add_left hright_v v
            _ = v * 2 := (mul_two v).symm)
      have hu'_gt_l : l < u' := by
        show l < (max u l + c) / 2
        have hl_left : l ≤ max u l := le_max_right u l
        exact (lt_div_iff₀ zero_lt_two).mpr
          (calc
            l * 2 = l + l := mul_two l
            _ ≤ l + max u l := add_le_add_left hl_left l
            _ = max u l + l := add_comm l (max u l)
            _ < max u l + c := add_lt_add_left hc_lr.1 (max u l))
      have hv'_lt_r : v' < r := by
        show (c + min v r) / 2 < r
        have hright_r : min v r ≤ r := min_le_right v r
        exact (div_lt_iff₀ zero_lt_two).mpr
          (calc
            c + min v r < r + min v r := add_lt_add_right hc_lr.2 (min v r)
            _ ≤ r + r := add_le_add_left hright_r r
            _ = r * 2 := (mul_two r).symm)
      have hgf_ae :
          g =ᵐ[MeasureTheory.volume.restrict (Ι u' v')] f := by
        have hne :
            ∀ᵐ x ∂MeasureTheory.volume.restrict (Ι u' v'), x ≠ c :=
          MeasureTheory.ae_restrict_of_ae
            ((Set.countable_singleton c).ae_not_mem MeasureTheory.volume)
        have hmem :
            ∀ᵐ x ∂MeasureTheory.volume.restrict (Ι u' v'),
              x ∈ Ι u' v' :=
          MeasureTheory.ae_restrict_mem measurableSet_uIoc
        exact
          (hne.and hmem).mono
            (fun x hx =>
              have hxc : x ≠ c := hx.1
              have hx_uIoc : x ∈ Ι u' v' := hx.2
              have hx_lr : x ∈ Set.Ioo l r := by
                have hx_Icc : x ∈ Set.Icc u' v' := by
                  have hx_Ioc : x ∈ Set.Ioc u' v' := by
                    have huv : u' < v' := hu'_c.trans hc_v'
                    exact
                      match Set.mem_uIoc.mp hx_uIoc with
                      | Or.inl hx_forward => hx_forward
                      | Or.inr hx_backward =>
                          False.elim
                            ((not_lt_of_ge hx_backward.2) (huv.trans hx_backward.1))
                  exact ⟨le_of_lt hx_Ioc.1, hx_Ioc.2⟩
                exact ⟨hu'_gt_l.trans_le hx_Icc.1, hx_Icc.2.trans_lt hv'_lt_r⟩
              (hsub_lr hx_lr hxc).symm)
      exact ⟨u', v', hu_u', hu'_c, hc_v', hv'_v, hgf_ae⟩

/-- Interval-integrability is unchanged when two functions agree on the
punctured neighborhood of the only point where the local model is singular.

The excluded point is null for Lebesgue measure, so the punctured equality is
enough for interval-integrability on a sufficiently small interval around the
center. -/
theorem intervalIntegrable_congr_of_eventuallyEq_nhdsWithin_punctured
    {f g : ℝ → ℝ}
    {c u v : ℝ}
    (huc : u < c)
    (hcv : c < v)
    (hfg : ∀ᶠ θ in 𝓝[≠] c, f θ = g θ)
    (hg : IntervalIntegrable g MeasureTheory.volume u v) :
    ∃ u' v' : ℝ,
      u < u' ∧ u' < c ∧ c < v' ∧ v' < v ∧
      IntervalIntegrable f MeasureTheory.volume u' v' := by
  match
      eventuallyEq_punctured_nhdsWithin_has_subinterval_aeEq
        (f := f) (g := g) huc hcv hfg
    with
  | ⟨u', v', hu_u', hu'_c, hc_v', hv'_v, hgf_ae⟩ =>
      have hu'_mem : u' ∈ [[u, v]] :=
        Set.mem_uIcc_of_le hu_u'.le (hu'_c.le.trans hcv.le)
      have hv'_mem : v' ∈ [[u, v]] :=
        Set.mem_uIcc_of_le (huc.le.trans hc_v'.le) hv'_v.le
      have hg_small : IntervalIntegrable g MeasureTheory.volume u' v' :=
        intervalIntegrable_mono_of_uIcc_endpoint_mem hg hu'_mem hv'_mem
      exact ⟨u', v', hu_u', hu'_c, hc_v', hv'_v, hg_small.congr hgf_ae⟩

/-- Local logarithmic model integrability on a smaller interval inside a
remainder-integrability interval. -/
theorem intervalIntegrable_log_singularity_model_eventually_on_subinterval
    (f : ℝ → ℝ)
    {c u v : ℝ}
    (n : ℕ)
    (g : ℝ → ℝ)
    (huc : u < c)
    (hcv : c < v)
    (hg : IntervalIntegrable g MeasureTheory.volume u v)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] c,
        f θ = (n : ℝ) * Real.log |θ - c| + g θ) :
    ∃ u' v' : ℝ,
      u < u' ∧ u' < c ∧ c < v' ∧ v' < v ∧
      IntervalIntegrable f MeasureTheory.volume u' v' := by
  have hcompact :
      IntervalIntegrable
        (fun x : ℝ => (n : ℝ) * Real.log |x - c| + g x)
        MeasureTheory.volume u v :=
    intervalIntegrable_log_singularity_model_on_compact
      n g huc.le hcv.le hg
  exact
    intervalIntegrable_congr_of_eventuallyEq_nhdsWithin_punctured
      huc hcv hmodel hcompact

/-- The compact-continuity base case of finite logarithmic-singularity gluing:
if there are no singular points in the compact interval, ordinary continuity on
that compact interval gives interval-integrability. -/
theorem intervalIntegrable_of_empty_log_singularities_on_compact
    (f : ℝ → ℝ)
    {a b : ℝ}
    (hab : a ≤ b)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ (∅ : Set ℝ)})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hcontIcc : ContinuousOn f (Set.Icc a b) := by
    exact hcont.mono
      (fun θ hθ => ⟨hθ, fun h => h⟩)
  exact hcontIcc.intervalIntegrable_of_Icc hab

/-- Local integrability near one logarithmic singularity from the punctured
local model and a locally integrable remainder.

This is the local owner cut used by the finite gluing theorem.  The point value
of `f` at `c` is irrelevant for interval integrability; on a small punctured
neighborhood, `f` agrees with the standard logarithmic model, and the model is
interval-integrable by `intervalIntegrable_log_singularity_model_on_compact`. -/
theorem intervalIntegrable_of_log_singularity_model_eventually_nhdsWithin
    (f : ℝ → ℝ)
    {c : ℝ}
    (n : ℕ)
    (g : ℝ → ℝ)
    (hg :
      ∃ u v : ℝ,
        u < c ∧ c < v ∧
        IntervalIntegrable g MeasureTheory.volume u v)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] c,
        f θ = (n : ℝ) * Real.log |θ - c| + g θ) :
    ∃ u v : ℝ,
      u < c ∧ c < v ∧
      IntervalIntegrable f MeasureTheory.volume u v := by
  match hg with
  | ⟨u, v, huc, hcv, hgint⟩ =>
      match
          intervalIntegrable_log_singularity_model_eventually_on_subinterval
            f n g huc hcv hgint hmodel
        with
      | ⟨u', v', _hu_u', hu'_c, hc_v', _hv'_v, hfint⟩ =>
          exact ⟨u', v', hu'_c, hc_v', hfint⟩

/-- Removing one point from a finite singular set leaves a finite singular set
on each compact side of the isolated point.  This is the finite-set separation
cut behind the compact gluing induction. -/
theorem finite_log_singularity_set_isolates_point_in_compact
    {a b c : ℝ}
    {S : Set ℝ}
    (hS : S.Finite)
    (hcS : c ∈ S) :
    ∃ u v : ℝ,
      u < c ∧ c < v ∧
      (Set.Ioo u v ∩ S) ⊆ {c} := by
  let T : Finset ℝ := hS.toFinset.erase c
  match Classical.decEq (Finset ℝ) T ∅ with
  | isTrue hT =>
      have hsubset :
          (Set.Ioo (c - 1) (c + 1) ∩ S) ⊆ {c} := by
        intro x hx
        have hxS : x ∈ S := hx.2
        exact Set.mem_singleton_iff.mpr
          (Classical.byContradiction
            (fun hxc =>
              have hxT : x ∈ T := by
                show x ∈ hS.toFinset.erase c
                have hxT0 : x ≠ c := hxc
                have hxSin : x ∈ hS.toFinset := by
                  exact hS.mem_toFinset.mpr hxS
                exact Finset.mem_erase.2 ⟨hxT0, hxSin⟩
              have hxEmpty : x ∈ (∅ : Finset ℝ) := by
                exact Eq.subst (motive := fun U : Finset ℝ => x ∈ U) hT hxT
              False.elim (Finset.not_mem_empty x hxEmpty)))
      exact ⟨c - 1, c + 1, sub_one_lt c, lt_add_one c, hsubset⟩
  | isFalse hT =>
      let D : Finset ℝ := T.image fun x => dist x c
      have hD : D.Nonempty := by
        match Finset.nonempty_iff_ne_empty.mpr hT with
        | ⟨x, hxT⟩ =>
            exact ⟨dist x c, Finset.mem_image.2 ⟨x, hxT, rfl⟩⟩
      have hDpos : 0 < D.min' hD := by
        have hmin_mem : D.min' hD ∈ D := Finset.min'_mem D hD
        match Finset.mem_image.1 hmin_mem with
        | ⟨x, hxT, hdist⟩ =>
            have hxc : x ≠ c := (Finset.mem_erase.1 hxT).1
            have hdist_pos : 0 < dist x c := dist_pos.2 hxc
            have hdist_eq : D.min' hD = dist x c := by
              exact hdist.symm
            calc
              0 < dist x c := hdist_pos
              _ = D.min' hD := hdist_eq.symm
      have hleft : c - D.min' hD / 2 < c :=
        sub_lt_self c (half_pos hDpos)
      have hright : c < c + D.min' hD / 2 :=
        lt_add_of_pos_right c (half_pos hDpos)
      have hsubset :
          (Set.Ioo (c - D.min' hD / 2) (c + D.min' hD / 2) ∩ S) ⊆ {c} := by
        intro x hx
        have hxS : x ∈ S := hx.2
        exact Set.mem_singleton_iff.mpr
          (Classical.byContradiction
            (fun hxc =>
              have hxT : x ∈ T := by
                show x ∈ hS.toFinset.erase c
                have hxT0 : x ≠ c := hxc
                have hxSin : x ∈ hS.toFinset := by
                  exact hS.mem_toFinset.mpr hxS
                exact Finset.mem_erase.2 ⟨hxT0, hxSin⟩
              have hxD : dist x c ∈ D := Finset.mem_image.2 ⟨x, hxT, rfl⟩
              have hmin_le : D.min' hD ≤ dist x c :=
                Finset.min'_le D (dist x c) hxD
              have hxleft : c - D.min' hD / 2 < x := hx.1.1
              have hxright : x < c + D.min' hD / 2 := hx.1.2
              have habs : |x - c| < D.min' hD := by
                have hhalf_lt : D.min' hD / 2 < D.min' hD :=
                  half_lt_self hDpos
                have hxc_half : x - c < D.min' hD / 2 :=
                  (sub_lt_iff_lt_add).mpr
                    (calc
                      x < c + D.min' hD / 2 := hxright
                      _ = D.min' hD / 2 + c := add_comm c (D.min' hD / 2))
                have hcx_half : c - x < D.min' hD / 2 := by
                  have hc_lt : c < x + D.min' hD / 2 :=
                    (sub_lt_iff_lt_add).mp hxleft
                  exact (sub_lt_iff_lt_add).mpr
                    (calc
                      c < x + D.min' hD / 2 := hc_lt
                      _ = D.min' hD / 2 + x := add_comm x (D.min' hD / 2))
                have hxc_lt : x - c < D.min' hD := lt_trans hxc_half hhalf_lt
                have hcx_lt : c - x < D.min' hD := lt_trans hcx_half hhalf_lt
                exact (abs_sub_lt_iff).2 ⟨hxc_lt, hcx_lt⟩
              have hdist_lt : dist x c < D.min' hD := by
                calc
                  dist x c = |x - c| := Real.dist_eq x c
                  _ < D.min' hD := habs
              False.elim ((not_lt_of_ge hmin_le) hdist_lt)))
      exact ⟨c - D.min' hD / 2, c + D.min' hD / 2, hleft, hright, hsubset⟩

/-- A locally interval-integrable neighborhood gives integrability at the
`Icc`-neighborhood filter of the center. -/
theorem integrableAtFilter_Icc_of_intervalIntegrable_neighborhood
    {f : ℝ → ℝ}
    {a b x u v : ℝ}
    (hux : u < x)
    (hxv : x < v)
    (hfint : IntervalIntegrable f MeasureTheory.volume u v) :
    IntegrableAtFilter f (𝓝[Set.Icc a b] x) MeasureTheory.volume := by
  have huv : u ≤ v := (hux.trans hxv).le
  have hIoo_nhds : Set.Ioo u v ∈ 𝓝 x :=
    Ioo_mem_nhds hux hxv
  have hIoc_nhds : Ι u v ∈ 𝓝 x := by
    exact mem_of_superset hIoo_nhds
      (fun y hy =>
        Set.Ioc_subset_uIoc (Set.mem_Ioc.2 ⟨hy.1, le_of_lt hy.2⟩))
  exact ⟨Ι u v, mem_nhdsWithin_of_mem_nhds hIoc_nhds, hfint.def'⟩

/-- At a point of `[a,b]` away from a finite singular set, continuity on the
finite-set complement gives integrability at the `[a,b]`-neighborhood filter. -/
theorem integrableAtFilter_Icc_of_continuousOn_finite_complement
    {f : ℝ → ℝ}
    {a b x : ℝ}
    {S : Set ℝ}
    (hS : S.Finite)
    (hxIcc : x ∈ Set.Icc a b)
    (hxS : x ∉ S)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntegrableAtFilter f (𝓝[Set.Icc a b] x) MeasureTheory.volume := by
  let K : Set ℝ := {θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S}
  have hxK : x ∈ K := ⟨hxIcc, hxS⟩
  have hKmeas : MeasurableSet K := by
    have hSclosed : IsClosed S := hS.isClosed
    exact measurableSet_Icc.inter hSclosed.isOpen_compl.measurableSet
  have hlocK : IntegrableAtFilter f (𝓝[K] x) MeasureTheory.volume :=
    (hcont.locallyIntegrableOn hKmeas) x hxK
  have hScompl_nhds : Sᶜ ∈ 𝓝 x :=
    hS.isClosed.isOpen_compl.mem_nhds hxS
  have hScompl_within : Sᶜ ∈ 𝓝[Set.Icc a b] x :=
    mem_nhdsWithin_of_mem_nhds hScompl_nhds
  have hfilter :
      𝓝[K] x = 𝓝[Set.Icc a b] x := by
    have hraw :
        𝓝[Set.Icc a b ∩ Sᶜ] x = 𝓝[Set.Icc a b] x :=
      nhdsWithin_inter_of_mem' hScompl_within
    exact hraw
  exact hfilter.symm ▸ hlocK

/-- Local integrability at every point of a compact ordered interval implies
interval-integrability on that interval. -/
theorem intervalIntegrable_of_locallyIntegrableOn_Icc
    {f : ℝ → ℝ}
    {a b : ℝ}
    (hab : a ≤ b)
    (hloc :
      MeasureTheory.LocallyIntegrableOn
        f (Set.Icc a b) MeasureTheory.volume) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hint : IntegrableOn f (Set.Icc a b) MeasureTheory.volume :=
    hloc.integrableOn_isCompact isCompact_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hint

/-- Gluing interval-integrability across a finite isolated singular set, once
each singular point has a locally integrable logarithmic model and the function
is continuous on the complement.

This is the measure-theoretic cover/gluing theorem behind the Jensen finite
singularity argument.  It contains no complex analysis: all analytic content has
already been reduced to local logarithmic models. -/
theorem intervalIntegrable_of_finite_log_singularity_cover
    (f : ℝ → ℝ)
    (a b : ℝ)
    (S : Set ℝ)
    (hab : a ≤ b)
    (hS : S.Finite)
    (hlocalInt :
      ∀ θ₀ ∈ S, ∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable f MeasureTheory.volume u v)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hloc :
      MeasureTheory.LocallyIntegrableOn
        f (Set.Icc a b) MeasureTheory.volume := by
    intro x hxIcc
    match Classical.dec (x ∈ S) with
    | isTrue hxS =>
        match hlocalInt x hxS with
        | ⟨u, v, hux, hxv, hfint⟩ =>
            exact
              integrableAtFilter_Icc_of_intervalIntegrable_neighborhood
                (a := a) (b := b) hux hxv hfint
    | isFalse hxS =>
        exact
          integrableAtFilter_Icc_of_continuousOn_finite_complement
            hS hxIcc hxS hcont
  exact intervalIntegrable_of_locallyIntegrableOn_Icc hab hloc

/-- Finite compact-interval gluing once each singular point has a logarithmic
local model and the complement is continuous.

The proof is by finite induction on `S`: the empty case is
`intervalIntegrable_of_empty_log_singularities_on_compact`; the step isolates
one singular point, uses
`intervalIntegrable_of_log_singularity_model_eventually_nhdsWithin` on the
central interval, applies the induction hypothesis to the two side intervals,
and glues the three interval-integrability statements by interval splitting. -/
theorem intervalIntegrable_of_finite_log_singularities_on_compact_glue
    (f : ℝ → ℝ)
    (a b : ℝ)
    (S : Set ℝ)
    (hab : a ≤ b)
    (hS : S.Finite)
    (hlocal :
      ∀ θ₀ ∈ S, ∃ n : ℕ, ∃ g : ℝ → ℝ,
        (∃ u v : ℝ,
          u < θ₀ ∧ θ₀ < v ∧
          IntervalIntegrable g MeasureTheory.volume u v) ∧
        ∀ᶠ θ in 𝓝[≠] θ₀,
          f θ = (n : ℝ) * Real.log |θ - θ₀| + g θ)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hlocalInt :
      ∀ θ₀ ∈ S, ∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable f MeasureTheory.volume u v := by
    intro θ₀ hθ₀
    match hlocal θ₀ hθ₀ with
    | ⟨n, g, hg, hmodel⟩ =>
        exact
          intervalIntegrable_of_log_singularity_model_eventually_nhdsWithin
            f n g hg hmodel
  exact
    intervalIntegrable_of_finite_log_singularity_cover
      f a b S hab hS hlocalInt hcont

/-- Finite compact-interval gluing for logarithmic singularities.

The local hypotheses say that every singular parameter has a punctured
neighborhood model `n * log |θ - θ₀| + g θ` with a locally integrable
remainder, and the complement is continuous.  The conclusion follows from the
interval integrability of the translated logarithm, local integrability of each
remainder, and finite interval gluing on `[a,b]`. -/
theorem intervalIntegrable_of_finite_log_singularities_on_compact
    (f : ℝ → ℝ)
    (a b : ℝ)
    (S : Set ℝ)
    (hab : a ≤ b)
    (hS : S.Finite)
    (hlocal :
      ∀ θ₀ ∈ S, ∃ n : ℕ, ∃ g : ℝ → ℝ,
        (∃ u v : ℝ,
          u < θ₀ ∧ θ₀ < v ∧
          IntervalIntegrable g MeasureTheory.volume u v) ∧
        ∀ᶠ θ in 𝓝[≠] θ₀,
          f θ = (n : ℝ) * Real.log |θ - θ₀| + g θ)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  exact
    intervalIntegrable_of_finite_log_singularities_on_compact_glue
      f a b S hab hS hlocal hcont

end
end LFunctions
end Boundary
