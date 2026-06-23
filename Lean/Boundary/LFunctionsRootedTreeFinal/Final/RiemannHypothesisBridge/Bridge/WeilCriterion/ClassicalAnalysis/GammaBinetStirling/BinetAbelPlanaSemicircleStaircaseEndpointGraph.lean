import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseEndpointMonotonicity

/-!
# Endpoint graph bounds for right semicircle staircases

This file owns the elementary min/max algebra and square-root transports used
to compare a right-semicircle graph value with endpoint graph values.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- Squaring preserves the minimum of two nonnegative real numbers as an
inequality toward the endpoint square minimum. -/
theorem min_sq_sq_le {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (min a b) ^ 2 ≤ min (a ^ 2) (b ^ 2) :=
  let hmin_nonneg : 0 ≤ min a b := le_min ha hb
  le_min
    (pow_le_pow_left₀ hmin_nonneg (min_le_left a b) 2)
    (pow_le_pow_left₀ hmin_nonneg (min_le_right a b) 2)

/-- Squaring preserves the minimum in the branch where the left endpoint is
smaller. -/
theorem min_sq_sq_of_le {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) :=
  let hmin : min a b = a := min_eq_left hab
  let hminsq : min (a ^ 2) (b ^ 2) = a ^ 2 :=
    min_eq_left (pow_le_pow_left₀ ha hab 2)
  calc
    (min a b) ^ 2 = a ^ 2 :=
      congrArg (fun x : ℝ => x ^ 2) hmin
    _ = min (a ^ 2) (b ^ 2) :=
      Eq.symm hminsq

/-- Squaring preserves the minimum in the branch where the right endpoint is
smaller. -/
theorem min_sq_sq_of_ge {a b : ℝ}
    (hb : 0 ≤ b)
    (hba : b ≤ a) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) :=
  let hmin : min a b = b := min_eq_right hba
  let hminsq : min (a ^ 2) (b ^ 2) = b ^ 2 :=
    min_eq_right (pow_le_pow_left₀ hb hba 2)
  calc
    (min a b) ^ 2 = b ^ 2 :=
      congrArg (fun x : ℝ => x ^ 2) hmin
    _ = min (a ^ 2) (b ^ 2) :=
      Eq.symm hminsq

/-- Squaring preserves the minimum of two nonnegative real numbers. -/
theorem min_sq_sq {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    [Decidable (a ≤ b)] :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) :=
  le_antisymm
    (min_sq_sq_le ha hb)
    (match (inferInstance : Decidable (a ≤ b)) with
    | isTrue hab =>
        le_of_eq (Eq.symm (min_sq_sq_of_le ha hab))
    | isFalse hnot =>
        le_of_eq (Eq.symm (min_sq_sq_of_ge hb (le_of_not_ge hnot))))

/-- Subtracting from a fixed real number turns endpoint minimum into endpoint
maximum in the left-smaller branch. -/
theorem max_sub_sub_left_eq_sub_min_of_le
    (a b c : ℝ)
    (hbc : b ≤ c) :
    max (a - b) (a - c) = a - (min b c) :=
  let hmin : min b c = b := min_eq_left hbc
  let hmax : max (a - b) (a - c) = a - b :=
    max_eq_left (sub_le_sub_left hbc a)
  calc
    max (a - b) (a - c) = a - b := hmax
    _ = a - (min b c) :=
      Eq.symm (congrArg (fun x : ℝ => a - x) hmin)

/-- Subtracting from a fixed real number turns endpoint minimum into endpoint
maximum in the right-smaller branch. -/
theorem max_sub_sub_left_eq_sub_min_of_ge
    (a b c : ℝ)
    (hcb : c ≤ b) :
    max (a - b) (a - c) = a - (min b c) :=
  let hmin : min b c = c := min_eq_right hcb
  let hmax : max (a - b) (a - c) = a - c :=
    max_eq_right (sub_le_sub_left hcb a)
  calc
    max (a - b) (a - c) = a - c := hmax
    _ = a - (min b c) :=
      Eq.symm (congrArg (fun x : ℝ => a - x) hmin)

/-- Subtracting from a fixed real number turns endpoint minimum into endpoint
maximum. -/
theorem max_sub_sub_left_eq_sub_min
    (a b c : ℝ)
    [Decidable (b ≤ c)] :
    max (a - b) (a - c) = a - (min b c) :=
  match (inferInstance : Decidable (b ≤ c)) with
  | isTrue hbc =>
      max_sub_sub_left_eq_sub_min_of_le a b c hbc
  | isFalse hnot =>
      max_sub_sub_left_eq_sub_min_of_ge a b c (le_of_not_ge hnot)

namespace Real

/-- Square-root distributes over binary maximum in the left-smaller branch. -/
theorem sqrt_max_of_le (a b : ℝ)
    (hab : a ≤ b) :
    Real.sqrt (max a b) = max (Real.sqrt a) (Real.sqrt b) :=
  let hmax : max a b = b := max_eq_right hab
  let hmaxsqrt : max (Real.sqrt a) (Real.sqrt b) = Real.sqrt b :=
    max_eq_right (Real.sqrt_le_sqrt hab)
  calc
    Real.sqrt (max a b) = Real.sqrt b :=
      congrArg Real.sqrt hmax
    _ = max (Real.sqrt a) (Real.sqrt b) :=
      Eq.symm hmaxsqrt

/-- Square-root distributes over binary maximum in the right-smaller branch. -/
theorem sqrt_max_of_ge (a b : ℝ)
    (hba : b ≤ a) :
    Real.sqrt (max a b) = max (Real.sqrt a) (Real.sqrt b) :=
  let hmax : max a b = a := max_eq_left hba
  let hmaxsqrt : max (Real.sqrt a) (Real.sqrt b) = Real.sqrt a :=
    max_eq_left (Real.sqrt_le_sqrt hba)
  calc
    Real.sqrt (max a b) = Real.sqrt a :=
      congrArg Real.sqrt hmax
    _ = max (Real.sqrt a) (Real.sqrt b) :=
      Eq.symm hmaxsqrt

/-- Square-root distributes over binary maximum. -/
theorem sqrt_max (a b : ℝ)
    [Decidable (a ≤ b)] :
    Real.sqrt (max a b) = max (Real.sqrt a) (Real.sqrt b) :=
  match (inferInstance : Decidable (a ≤ b)) with
  | isTrue hab =>
      Real.sqrt_max_of_le a b hab
  | isFalse hnot =>
      Real.sqrt_max_of_ge a b (le_of_not_ge hnot)

end Real

/-- Squaring absolute values commutes with taking the endpoint minimum. -/
theorem min_sq_eq_min_abs_sq
    (y₀ y₁ : ℝ)
    [Decidable (|y₀| ≤ |y₁|)] :
    min (y₀ ^ 2) (y₁ ^ 2) = min |y₀| |y₁| ^ 2 :=
  let hleft : y₀ ^ 2 = |y₀| ^ 2 :=
    Eq.symm (sq_abs y₀)
  let hright : y₁ ^ 2 = |y₁| ^ 2 :=
    Eq.symm (sq_abs y₁)
  calc
    min (y₀ ^ 2) (y₁ ^ 2) = min (|y₀| ^ 2) (|y₁| ^ 2) :=
      congrArg₂ min hleft hright
    _ = min |y₀| |y₁| ^ 2 :=
      Eq.symm (min_sq_sq (abs_nonneg y₀) (abs_nonneg y₁))

/-- The squared-radius expression at a point is bounded by the maximum of the
endpoint squared-radius expressions when the point is farther from zero than
the nearer endpoint. -/
theorem radius_sub_sq_le_endpoint_max_sub_sq_of_min_sq_le
    (ρ y₀ y₁ y : ℝ)
    [Decidable (y₀ ^ 2 ≤ y₁ ^ 2)]
    (hsq_ge : min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2) :
    ρ ^ 2 - y ^ 2 ≤ max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) :=
  let hmax_sub :
      max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) =
        ρ ^ 2 - (min (y₀ ^ 2) (y₁ ^ 2)) :=
    max_sub_sub_left_eq_sub_min (ρ ^ 2) (y₀ ^ 2) (y₁ ^ 2)
  calc
    ρ ^ 2 - y ^ 2 ≤ ρ ^ 2 - (min (y₀ ^ 2) (y₁ ^ 2)) :=
      sub_le_sub_left hsq_ge (ρ ^ 2)
    _ = max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) :=
      Eq.symm hmax_sub

/-- Square-root transports the squared-radius endpoint maximum bound to the
corresponding graph-coordinate maximum bound. -/
theorem sqrt_radius_sub_sq_le_endpoint_sqrt_max_of_min_sq_le
    (ρ y₀ y₁ y : ℝ)
    [Decidable (y₀ ^ 2 ≤ y₁ ^ 2)]
    [Decidable (ρ ^ 2 - y₀ ^ 2 ≤ ρ ^ 2 - y₁ ^ 2)]
    (hsq_ge : min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2) :
    Real.sqrt (ρ ^ 2 - y ^ 2) ≤
      max (Real.sqrt (ρ ^ 2 - y₀ ^ 2))
        (Real.sqrt (ρ ^ 2 - y₁ ^ 2)) :=
  let hrad_le_endpoint :
      ρ ^ 2 - y ^ 2 ≤ max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) :=
    radius_sub_sq_le_endpoint_max_sub_sq_of_min_sq_le ρ y₀ y₁ y hsq_ge
  let hmax_sqrt :
      Real.sqrt (max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2)) =
        max (Real.sqrt (ρ ^ 2 - y₀ ^ 2))
          (Real.sqrt (ρ ^ 2 - y₁ ^ 2)) :=
    Real.sqrt_max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2)
  calc
    Real.sqrt (ρ ^ 2 - y ^ 2) ≤
        Real.sqrt (max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2)) :=
      Real.sqrt_le_sqrt hrad_le_endpoint
    _ = max (Real.sqrt (ρ ^ 2 - y₀ ^ 2))
          (Real.sqrt (ρ ^ 2 - y₁ ^ 2)) :=
      hmax_sqrt

/-- If the vertical coordinate is at least as far from zero as the nearer
endpoint, the right semicircle graph is bounded by the endpoint maximum. -/
theorem Complex.rightSemicircleGraphRe_le_endpointMax_of_min_sq_le
    (ρ y₀ y₁ y : ℝ)
    [Decidable (y₀ ^ 2 ≤ y₁ ^ 2)]
    [Decidable (ρ ^ 2 - y₀ ^ 2 ≤ ρ ^ 2 - y₁ ^ 2)]
    (hsq_ge : min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2) :
    Complex.rightSemicircleGraphRe ρ y ≤
      max (Complex.rightSemicircleGraphRe ρ y₀)
        (Complex.rightSemicircleGraphRe ρ y₁) :=
  let hgraph_lhs :
      Complex.rightSemicircleGraphRe ρ y =
        Real.sqrt (ρ ^ 2 - y ^ 2) :=
    Complex.rightSemicircleGraphRe_eq_sqrt ρ y
  let hgraph_y₀ :
      Complex.rightSemicircleGraphRe ρ y₀ =
        Real.sqrt (ρ ^ 2 - y₀ ^ 2) :=
    Complex.rightSemicircleGraphRe_eq_sqrt ρ y₀
  let hgraph_y₁ :
      Complex.rightSemicircleGraphRe ρ y₁ =
        Real.sqrt (ρ ^ 2 - y₁ ^ 2) :=
    Complex.rightSemicircleGraphRe_eq_sqrt ρ y₁
  let hsqrt :
      Real.sqrt (ρ ^ 2 - y ^ 2) ≤
        max (Real.sqrt (ρ ^ 2 - y₀ ^ 2))
          (Real.sqrt (ρ ^ 2 - y₁ ^ 2)) :=
    sqrt_radius_sub_sq_le_endpoint_sqrt_max_of_min_sq_le ρ y₀ y₁ y hsq_ge
  Eq.mpr
    (congrArg₂
      (fun lhs rhs : ℝ => lhs ≤ rhs)
      hgraph_lhs.symm
      (congrArg₂ max hgraph_y₀.symm hgraph_y₁.symm))
    hsqrt

end

end LFunctions
end Boundary
