import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Order.Interval.Set.UnorderedInterval
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.BernoulliCore

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory Filter
local notation "π" => Real.pi

theorem real_natCast_le_of_nat_le
    {m n : ℕ}
    (hmn : m ≤ n) :
    ((m : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) :=
  Nat.cast_le.mpr hmn

/-- Splitting the strict natural endpoint sum at the last endpoint. -/
theorem eulerMaclaurin_sum_Ioc_succ_top
    (f : ℕ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M) :
    (∑ n in Finset.Ioc N (M + 1), f n) =
      (∑ n in Finset.Ioc N M, f n) + f (M + 1) := by
  calc
    ∑ n in Finset.Ioc N (M + 1), f n =
        ∑ n in Finset.Ioc N M, f n + ∑ n in Finset.Ioc M (M + 1), f n := by
      exact (Finset.sum_Ioc_consecutive f hNM (Nat.le_succ M)).symm
    _ = ∑ n in Finset.Ioc N M, f n + f (M + 1) := by
      have htop : Finset.Ioc M (M + 1) = ({M + 1} : Finset ℕ) := by
        exact Nat.Ioc_succ_singleton M
      have hsum_transport :
          ∑ n in Finset.Ioc M (M + 1), f n =
            ∑ n in ({M + 1} : Finset ℕ), f n :=
        congrArg (fun s : Finset ℕ => ∑ n in s, f n) htop
      calc
        ∑ n in Finset.Ioc N M, f n + ∑ n in Finset.Ioc M (M + 1), f n
            = ∑ n in Finset.Ioc N M, f n + ∑ n in ({M + 1} : Finset ℕ), f n := by
              exact congrArg
                (fun x : ℂ => ∑ n in Finset.Ioc N M, f n + x)
                hsum_transport
        _ = ∑ n in Finset.Ioc N M, f n + f (M + 1) := by
              exact congrArg
                (fun x : ℂ => ∑ n in Finset.Ioc N M, f n + x)
                (Finset.sum_singleton f (M + 1))

/-- Splitting a set integral over adjacent natural `Ioc` intervals. -/
theorem eulerMaclaurin_integral_Ioc_succ_top
    (g : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hg_left : IntegrableOn g
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hg_right : IntegrableOn g
      (Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))), g x) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), g x) +
        (∫ x in Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))), g x) := by
  let a : ℝ := ((N : ℕ) : ℝ)
  let b : ℝ := ((M : ℕ) : ℝ)
  let c : ℝ := (((M + 1 : ℕ) : ℝ))
  have hab : a ≤ b := by
    exact Nat.cast_le.mpr hNM
  have hbc : b ≤ c := by
    exact Nat.cast_le.mpr (Nat.le_succ M)
  have hleft_interval : IntervalIntegrable g volume a b := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        hg_left
  have hright_interval : IntervalIntegrable g volume b c := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hbc).mpr
        hg_right
  have hconcat :
      (∫ x in a..b, g x) + (∫ x in b..c, g x) =
        ∫ x in a..c, g x :=
    intervalIntegral.integral_add_adjacent_intervals
      hleft_interval hright_interval
  have hleft_set :
      (∫ x in a..b, g x) =
        ∫ x in Set.Ioc a b, g x :=
    intervalIntegral.integral_of_le hab
  have hright_set :
      (∫ x in b..c, g x) =
        ∫ x in Set.Ioc b c, g x :=
    intervalIntegral.integral_of_le hbc
  have hac : a ≤ c := le_trans hab hbc
  have hwhole_set :
      (∫ x in a..c, g x) =
        ∫ x in Set.Ioc a c, g x :=
    intervalIntegral.integral_of_le hac
  have hset :
      (∫ x in Set.Ioc a c, g x) =
        (∫ x in Set.Ioc a b, g x) +
          (∫ x in Set.Ioc b c, g x) := by
    exact Eq.trans hwhole_set.symm
      (Eq.trans hconcat.symm
        (congrArg₂ HAdd.hAdd hleft_set hright_set))
  exact hset

/-- Endpoint half-corrections telescope in the last-step induction for the
strict-right Euler-Maclaurin convention. -/
theorem eulerMaclaurin_endpoint_half_telescope_succ
    (f : ℕ → ℂ)
    (N M : ℕ) :
    (-(1 / 2 : ℂ) * f N) + ((1 / 2 : ℂ) * f M) +
        (-(1 / 2 : ℂ) * f M) + ((1 / 2 : ℂ) * f (M + 1)) =
    (-(1 / 2 : ℂ) * f N) + ((1 / 2 : ℂ) * f (M + 1)) := by
  let A : ℂ := -(1 / 2 : ℂ) * f N
  let B : ℂ := (1 / 2 : ℂ) * f M
  let D : ℂ := (1 / 2 : ℂ) * f (M + 1)
  have hnegB :
      (-(1 / 2 : ℂ) * f M) = -B := by
    calc
      (-(1 / 2 : ℂ) * f M) = -((1 / 2 : ℂ) * f M) := by
        exact neg_mul (1 / 2 : ℂ) (f M)
      _ = -B := by
        exact congrArg Neg.neg rfl
  have hcancel : B + (-B) = 0 :=
    add_neg_cancel B
  calc
    (-(1 / 2 : ℂ) * f N) + ((1 / 2 : ℂ) * f M) +
        (-(1 / 2 : ℂ) * f M) + ((1 / 2 : ℂ) * f (M + 1))
        = (A + B) + (-B) + D := by
          exact congrArg₂
            (fun X Y : ℂ => (A + B) + X + Y)
            hnegB
            rfl
    _ = A + (B + (-B)) + D := by
      exact congrArg (fun X : ℂ => X + D) (add_assoc A B (-B))
    _ = A + 0 + D := by
      exact congrArg (fun X : ℂ => A + X + D) hcancel
    _ = A + D := by
      exact congrArg (fun X : ℂ => X + D) (add_zero A)
    _ = (-(1 / 2 : ℂ) * f N) + ((1 / 2 : ℂ) * f (M + 1)) := by
      rfl

/-- Continuity on a larger natural closed interval restricts to the left subinterval. -/
theorem eulerMaclaurin_continuousOn_Icc_left_of_succ
    (f : ℝ → ℂ)
    (N M : ℕ)
    (_hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))))) :
    ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
  exact hf_cont.mono
    (fun x hx => by
      constructor
      · exact hx.1
      · exact le_trans hx.2 (real_natCast_le_of_nat_le (Nat.le_succ M)))

/-- Continuity on a larger natural closed interval restricts to the last
unit closed subinterval. -/
theorem eulerMaclaurin_continuousOn_Icc_right_of_succ
    (f : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))))) :
    ContinuousOn f
      (Set.Icc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ)))) := by
  exact hf_cont.mono
    (fun x hx => by
      constructor
      · exact le_trans (real_natCast_le_of_nat_le hNM) hx.1
      · exact hx.2)

/-- The open left subinterval inherits the derivative hypothesis from the
larger natural open interval. -/
theorem eulerMaclaurin_deriv_Ioo_left_of_succ
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))) →
        HasDerivAt f (f' x) x) :
    ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x := by
  intro x hx
  exact hf_deriv x
    ⟨hx.1, lt_of_lt_of_le hx.2 (real_natCast_le_of_nat_le (Nat.le_succ M))⟩

/-- The last unit open subinterval inherits the derivative hypothesis from the
larger natural open interval. -/
theorem eulerMaclaurin_deriv_Ioo_right_of_succ
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))) →
        HasDerivAt f (f' x) x) :
    ∀ x : ℝ,
      x ∈ Set.Ioo (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))) →
        HasDerivAt f (f' x) x := by
  intro x hx
  exact hf_deriv x
    ⟨lt_of_le_of_lt (real_natCast_le_of_nat_le hNM) hx.1, hx.2⟩

/-- Integrability on a larger natural `Ioc` interval restricts to the left
subinterval. -/
theorem eulerMaclaurin_integrableOn_Ioc_left_of_succ
    (g : ℝ → ℂ)
    (N M : ℕ)
    (_hNM : N ≤ M)
    (hg : IntegrableOn g
      (Set.Ioc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))))) :
    IntegrableOn g
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
  exact hg.mono_set
    (fun x hx => by
      exact ⟨hx.1, le_trans hx.2 (real_natCast_le_of_nat_le (Nat.le_succ M))⟩)

/-- Integrability on a larger natural `Ioc` interval restricts to the last unit
`Ioc` interval. -/
theorem eulerMaclaurin_integrableOn_Ioc_right_of_succ
    (g : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hg : IntegrableOn g
      (Set.Ioc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))))) :
    IntegrableOn g
      (Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ)))) := by
  exact hg.mono_set
    (fun x hx => by
      exact ⟨lt_of_le_of_lt (real_natCast_le_of_nat_le hNM) hx.1, hx.2⟩)

/-- Multiplication by the bounded first-periodic Bernoulli factor preserves
finite `Ioc` integrability. -/
theorem eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
    (g : ℝ → ℂ)
    (A B : ℝ)
    (hg : IntegrableOn g (Set.Ioc A B)) :
    IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * g x)
      (Set.Ioc A B) := by
  let s : Set ℝ := Set.Ioc A B
  have hg_integrable : Integrable g (volume.restrict s) := by
    exact hg
  have hB_meas :
      AEStronglyMeasurable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
        (volume.restrict s) :=
    eulerMaclaurinFirstPeriodicBernoulli_cast_aestronglyMeasurable_restrict_finite
      s measurableSet_Ioc
  have hB_bound :
      ∃ C : ℝ,
        ∀ x : ℝ,
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ C := by
    exact ⟨1, eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite⟩
  have hmul :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * g x)
        (volume.restrict s) :=
    Integrable.bdd_mul hg_integrable hB_meas hB_bound
  exact hmul

/-- Base case for the finite first-periodic-Bernoulli Euler-Maclaurin sum:
the strict interval `(N, N]` is empty and the endpoint half-terms cancel. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc_base
    (f f' : ℝ → ℂ)
    (N : ℕ) :
    (∑ n in Finset.Ioc N N, f ((n : ℕ) : ℝ)) =
    (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((N : ℕ) : ℝ)), f x) +
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  have hsum_empty_set :
      Finset.Ioc N N = ∅ :=
    Finset.Ioc_eq_empty_of_le le_rfl
  have hsum_zero :
      (∑ n in Finset.Ioc N N, f ((n : ℕ) : ℝ)) = 0 := by
    exact Eq.trans
      (congrArg
        (fun s : Finset ℕ => ∑ n in s, f ((n : ℕ) : ℝ))
        hsum_empty_set)
      (Finset.sum_empty)
  have hinterval_empty :
      Set.Ioc (((N : ℕ) : ℝ)) (((N : ℕ) : ℝ)) = ∅ :=
    Set.Ioc_eq_empty_of_le le_rfl
  have hintegral_f_zero :
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((N : ℕ) : ℝ)), f x) = 0 := by
    exact Eq.subst
      (motive := fun s : Set ℝ => (∫ x in s, f x) = 0)
      hinterval_empty.symm
      (setIntegral_empty (f := f) (μ := volume))
  have hkernel_zero :
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) = 0 := by
    exact Eq.subst
      (motive := fun s : Set ℝ =>
        (∫ x in s, ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) = 0)
      hinterval_empty.symm
      (setIntegral_empty
        (μ := volume)
        (f := fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x))
  have hhalf_cancel :
      (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) = 0 := by
    have hneg :
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) =
          -((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) :=
      neg_mul (1 / 2 : ℂ) (f (((N : ℕ) : ℝ)))
    calc
      (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) =
          -((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
            ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) := by
        exact congrArg
          (fun x : ℂ => x + ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))))
          hneg
      _ = 0 := by
        exact neg_add_cancel ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ)))
  calc
    (∑ n in Finset.Ioc N N, f ((n : ℕ) : ℝ)) = 0 :=
      hsum_zero
    _ = 0 + (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ)) +
          (1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) + 0 := by
      calc
        (0 : ℂ) = 0 + 0 + 0 := by
          exact Eq.trans (zero_add (0 : ℂ)).symm (add_zero (0 + (0 : ℂ))).symm
        _ = 0 + (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ)) +
              (1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) + 0 := by
          exact congrArg
            (fun x : ℂ => 0 + x + 0)
            hhalf_cancel.symm
    _ = 0 + (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) + 0 := by
      exact congrArg
        (fun x : ℂ => x + 0)
        (add_assoc
          (0 : ℂ)
          (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ)))
          ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ)))).symm
    _ =
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((N : ℕ) : ℝ)), f x) +
          (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
      exact congrArg₂
        (fun X Y : ℂ =>
          X + (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
            ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) + Y)
        hintegral_f_zero.symm
        hkernel_zero.symm

/-- A named additive rebracketing for the successor Euler--Maclaurin assembly. -/
theorem eulerMaclaurin_successor_additive_rebracket
    (a b c d e f g h : ℂ) :
    (a + b + c + d) + (e + f + (g + h)) =
      (a + e) + ((b + c) + f + g) + (d + h) := by
  calc
    (a + b + c + d) + (e + f + (g + h))
        = (a + b + c) + (e + f) + (d + (g + h)) := by
          exact add_add_add_comm (a + b + c) d (e + f) (g + h)
    _ = ((a + b) + e) + (c + f) + (d + (g + h)) := by
          exact congrArg
            (fun X : ℂ => X + (d + (g + h)))
            (add_add_add_comm (a + b) c e f)
    _ = (a + b) + (e + (c + f)) + (d + (g + h)) := by
          exact congrArg
            (fun X : ℂ => X + (d + (g + h)))
            (add_assoc (a + b) e (c + f))
    _ = (a + e) + (b + (c + f)) + (d + (g + h)) := by
          exact congrArg
            (fun X : ℂ => X + (d + (g + h)))
            (add_add_add_comm a b e (c + f))
    _ = (a + e) + ((b + c) + f) + (d + (g + h)) := by
          exact congrArg
            (fun X : ℂ => (a + e) + X + (d + (g + h)))
            ((add_assoc b c f).symm)
    _ = (a + e) + ((b + c) + f) + (g + (d + h)) := by
          exact congrArg
            (fun X : ℂ => (a + e) + ((b + c) + f) + X)
            (add_left_comm d g h)
    _ = (a + e) + (((b + c) + f) + g) + (d + h) := by
          calc
            (a + e) + ((b + c) + f) + (g + (d + h))
                = (a + e) + (((b + c) + f) + (g + (d + h))) := by
                  exact add_assoc (a + e) ((b + c) + f) (g + (d + h))
            _ = (a + e) + ((((b + c) + f) + g) + (d + h)) := by
                  exact congrArg
                    (fun X : ℂ => (a + e) + X)
                    ((add_assoc ((b + c) + f) g (d + h)).symm)
            _ = (a + e) + (((b + c) + f) + g) + (d + h) := by
                  exact
                    (add_assoc (a + e) (((b + c) + f) + g) (d + h)).symm

/-- Successor step for the finite first-periodic-Bernoulli Euler-Maclaurin
sum. This owns the finite partition and endpoint-telescoping assembly,
assuming the formula has already been proved on the left interval. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc_succ
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hleft :
      (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
          (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x))
    (hright :
      f ((((M + 1 : ℕ) : ℝ))) =
        (∫ x in Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))), f x) +
          (-(1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f ((((M + 1 : ℕ) : ℝ))) +
          (∫ x in Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)))
    (hf_left_int : IntegrableOn f
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_right_int : IntegrableOn f
      (Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ)))))
    (hrem_left_int : IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hrem_right_int : IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)
      (Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))))) :
    (∑ n in Finset.Ioc N (M + 1), f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))), f x) +
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f ((((M + 1 : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)) := by
  let FN : ℂ := f (((N : ℕ) : ℝ))
  let FM : ℂ := f (((M : ℕ) : ℝ))
  let FM1 : ℂ := f ((((M + 1 : ℕ) : ℝ)))
  let Lf : ℂ := ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x
  let Rf : ℂ := ∫ x in Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))), f x
  let Lr : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x
  let Rr : ℂ :=
    ∫ x in Set.Ioc (((M : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x
  let Wf : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))), f x
  let Wr : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((M + 1 : ℕ) : ℝ))),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x
  have hsum_split :
      (∑ n in Finset.Ioc N (M + 1), f ((n : ℕ) : ℝ)) =
        (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) + FM1 :=
    eulerMaclaurin_sum_Ioc_succ_top
      (fun n : ℕ => f ((n : ℕ) : ℝ)) N M hNM
  have hf_integral_split :
      Wf = Lf + Rf :=
    eulerMaclaurin_integral_Ioc_succ_top f N M hNM
      hf_left_int hf_right_int
  have hrem_integral_split :
      Wr = Lr + Rr :=
    eulerMaclaurin_integral_Ioc_succ_top
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)
      N M hNM hrem_left_int hrem_right_int
  have hendpoints :
      (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM) +
          (-(1 / 2 : ℂ) * FM) + ((1 / 2 : ℂ) * FM1) =
        (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1) :=
    eulerMaclaurin_endpoint_half_telescope_succ
      (fun n : ℕ => f ((n : ℕ) : ℝ)) N M
  have hleft_named :
      (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
        Lf + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM) + Lr :=
    hleft
  have hright_named :
      FM1 =
        Rf + (-(1 / 2 : ℂ) * FM) + ((1 / 2 : ℂ) * FM1 + Rr) :=
    hright
  have hassembled :
      (Lf + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM) + Lr) +
          (Rf + (-(1 / 2 : ℂ) * FM) + ((1 / 2 : ℂ) * FM1 + Rr)) =
        (Lf + Rf) + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1 + (Lr + Rr)) := by
    calc
      (Lf + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM) + Lr) +
          (Rf + (-(1 / 2 : ℂ) * FM) + ((1 / 2 : ℂ) * FM1 + Rr))
          = (Lf + Rf) +
              (((-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM)) +
                (-(1 / 2 : ℂ) * FM) + ((1 / 2 : ℂ) * FM1)) +
              (Lr + Rr) := by
        exact eulerMaclaurin_successor_additive_rebracket
          Lf (-(1 / 2 : ℂ) * FN) ((1 / 2 : ℂ) * FM) Lr
          Rf (-(1 / 2 : ℂ) * FM) ((1 / 2 : ℂ) * FM1) Rr
      _ = (Lf + Rf) + ((-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1)) +
              (Lr + Rr) := by
        exact congrArg
          (fun X : ℂ => (Lf + Rf) + X + (Lr + Rr))
          hendpoints
      _ = (Lf + Rf) + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1 + (Lr + Rr)) := by
        calc
          (Lf + Rf) + ((-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1)) +
              (Lr + Rr)
              = ((Lf + Rf) + (-(1 / 2 : ℂ) * FN)) +
                  ((1 / 2 : ℂ) * FM1) + (Lr + Rr) := by
            exact congrArg
              (fun X : ℂ => X + (Lr + Rr))
              (add_assoc (Lf + Rf) (-(1 / 2 : ℂ) * FN) ((1 / 2 : ℂ) * FM1)).symm
          _ = (Lf + Rf) + (-(1 / 2 : ℂ) * FN) +
                (((1 / 2 : ℂ) * FM1) + (Lr + Rr)) := by
            exact add_assoc ((Lf + Rf) + (-(1 / 2 : ℂ) * FN)) ((1 / 2 : ℂ) * FM1) (Lr + Rr)
  calc
    (∑ n in Finset.Ioc N (M + 1), f ((n : ℕ) : ℝ)) =
        (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) + FM1 :=
      hsum_split
    _ =
        (Lf + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM) + Lr) +
          (Rf + (-(1 / 2 : ℂ) * FM) + ((1 / 2 : ℂ) * FM1 + Rr)) := by
      exact congrArg₂ HAdd.hAdd hleft_named hright_named
    _ = (Lf + Rf) + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1 + (Lr + Rr)) :=
      hassembled
    _ =
      Wf + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1 + Wr) := by
      exact congrArg₂
        (fun X Y : ℂ => X + (-(1 / 2 : ℂ) * FN) + ((1 / 2 : ℂ) * FM1 + Y))
        hf_integral_split.symm
        hrem_integral_split.symm

end
end LFunctions
end Boundary
