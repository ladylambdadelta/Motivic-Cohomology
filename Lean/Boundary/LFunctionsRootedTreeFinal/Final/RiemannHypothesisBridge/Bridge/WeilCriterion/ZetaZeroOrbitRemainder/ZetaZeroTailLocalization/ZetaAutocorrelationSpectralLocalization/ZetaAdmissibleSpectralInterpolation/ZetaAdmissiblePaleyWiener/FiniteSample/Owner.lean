import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner

/-!
# Paley-Wiener finite sample interpolation

This file owns the finite Laplace-sample map, Kronecker cardinal vectors, dual
separation, and finite Paley-Wiener interpolation wrappers. It is copy-first
extracted from the current Paley-Wiener owner file and is not imported by that
parent yet, so declaration names intentionally match the existing owner surface.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction

/-- The finite Laplace-transform sample vector of an admissible function. -/
def zetaLaplaceTransformFiniteSample
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    S → ℂ :=
  fun z : S => Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ)

/-- The finite target vector induced by a function on the ambient spectral plane. -/
def zetaLaplaceTransformFiniteTarget
    (S : Finset ℂ) (a : ℂ → ℂ) :
    S → ℂ :=
  fun z : S => a (z : ℂ)

/-- The finite Laplace-sample vector of a scalar multiple is the scalar multiple of the
finite Laplace-sample vector. -/
theorem zetaLaplaceTransformFiniteSample_smul
    (S : Finset ℂ) (c : ℂ) (f : ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (c • f) =
      c • zetaLaplaceTransformFiniteSample S f := by
  funext z
  unfold zetaLaplaceTransformFiniteSample
  have hpoint :
      (c • f).toZetaTestFunction' =
        c • f.toZetaTestFunction' := by
    ext t
    calc
      (c • f).toZetaTestFunction' t =
          (c • f) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (c • f) t
      _ = c * f t := by
        exact ZetaAdmissibleFunction.smul_apply c f t
      _ = c * f.toZetaTestFunction' t := by
        exact congrArg (fun u : ℂ => c * u)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
      _ = (c • f.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (c • f).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform (c • f.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrFun hpoint t)) (z : ℂ)
    _ = c * Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_smul c f.toZetaTestFunction' (z : ℂ)
    _ = (c • zetaLaplaceTransformFiniteSample S f) z := by
      rfl

/-- The finite Laplace-sample vector of a sum is the sum of the finite Laplace-sample
vectors. -/
theorem zetaLaplaceTransformFiniteSample_add
    (S : Finset ℂ) (f g : ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (f + g) =
      zetaLaplaceTransformFiniteSample S f +
        zetaLaplaceTransformFiniteSample S g := by
  funext z
  unfold zetaLaplaceTransformFiniteSample
  have hpoint :
      (f + g).toZetaTestFunction' =
        f.toZetaTestFunction' + g.toZetaTestFunction' := by
    ext t
    calc
      (f + g).toZetaTestFunction' t =
          (f + g) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (f + g) t
      _ = f t + g t := by
        exact ZetaAdmissibleFunction.add_apply f g t
      _ = f.toZetaTestFunction' t + g.toZetaTestFunction' t := by
        exact congrArg₂ (fun u v : ℂ => u + v)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply g t).symm
      _ = (f.toZetaTestFunction' + g.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (f + g).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform
          (f.toZetaTestFunction' + g.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrFun hpoint t)) (z : ℂ)
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) +
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_add
        f.toZetaTestFunction'
        g.toZetaTestFunction'
        (z : ℂ)
        (integrable_laplaceKernel_at f (z : ℂ))
        (integrable_laplaceKernel_at g (z : ℂ))
    _ =
        (zetaLaplaceTransformFiniteSample S f +
          zetaLaplaceTransformFiniteSample S g) z := by
      rfl

/-- The finite Laplace-sample map as a bundled linear map. -/
def zetaLaplaceTransformFiniteSampleLinearMap
    (S : Finset ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ] (S → ℂ) where
  toFun := zetaLaplaceTransformFiniteSample S
  map_add' := fun f g =>
    zetaLaplaceTransformFiniteSample_add S f g
  map_smul' := fun c f =>
    zetaLaplaceTransformFiniteSample_smul S c f

/-- The finite Laplace-sample vector of a finite sum is the finite sum of the sample
vectors. -/
theorem zetaLaplaceTransformFiniteSample_sum
    {α : Type*} [DecidableEq α]
    (S : Finset ℂ) (T : Finset α) (F : α → ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (∑ x in T, F x) =
      ∑ x in T, zetaLaplaceTransformFiniteSample S (F x) := by
  funext z
  unfold zetaLaplaceTransformFiniteSample
  have hpoint :
      (∑ x in T, F x).toZetaTestFunction' =
        ∑ x in T, (F x).toZetaTestFunction' := by
    ext t
    calc
      (∑ x in T, F x).toZetaTestFunction' t =
          (∑ x in T, F x) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (∑ x in T, F x) t
      _ = ∑ x in T, F x t := by
        exact ZetaAdmissibleFunction.sum_apply T F t
      _ = (∑ x in T, (F x).toZetaTestFunction') t := by
        exact (Boundary.zetaLaplaceTransform_sum_apply
          (s := T)
          (f := fun x : α => (F x).toZetaTestFunction')
          t).symm
  calc
    Boundary.zetaLaplaceTransform (∑ x in T, F x).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform (∑ x in T, (F x).toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrFun hpoint t)) (z : ℂ)
    _ =
        ∑ x in T,
          Boundary.zetaLaplaceTransform (F x).toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_sum
        T
        (fun x : α => (F x).toZetaTestFunction')
        (z : ℂ)
        (fun x _hx => integrable_laplaceKernel_at (F x) (z : ℂ))
    _ = (∑ x in T, zetaLaplaceTransformFiniteSample S (F x)) z := by
      exact (T.sum_apply z
        (fun x : α => zetaLaplaceTransformFiniteSample S (F x))).symm

/-- A cardinal family gives the finite linear-combination interpolant for any target
finite sample vector. -/
theorem zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
    (S : Finset ℂ) (aS : S → ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    zetaLaplaceTransformFiniteSample S (∑ z : S, aS z • F z) = aS := by
  classical
  funext w
  calc
    zetaLaplaceTransformFiniteSample S (∑ z : S, aS z • F z) w =
        (∑ z : S, zetaLaplaceTransformFiniteSample S (aS z • F z)) w := by
      exact congrFun
        (zetaLaplaceTransformFiniteSample_sum
          S Finset.univ (fun z : S => aS z • F z))
        w
    _ =
        ∑ z : S, zetaLaplaceTransformFiniteSample S (aS z • F z) w := by
      exact Finset.univ.sum_apply w
        (fun z : S => zetaLaplaceTransformFiniteSample S (aS z • F z))
    _ =
        ∑ z : S, aS z *
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrFun (zetaLaplaceTransformFiniteSample_smul S (aS z) (F z)) w)
    _ =
        ∑ z : S, aS z * (if w = z then 1 else 0) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u) (hF z w))
    _ = aS w := by
      have hsingle :
          ∑ z in (Finset.univ : Finset S),
              aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
        exact Finset.sum_eq_single
          (a := w)
          (f := fun z : S => aS z * (if w = z then 1 else 0))
          (fun z _hz hzw =>
            have hne : w ≠ z := fun hwz => hzw hwz.symm
            calc
              aS z * (if w = z then 1 else 0) =
                  aS z * 0 := by
                exact congrArg (fun u : ℂ => aS z * u) (if_neg hne)
              _ = 0 := by
                exact mul_zero (aS z))
          (fun hw =>
            False.elim (hw (Finset.mem_univ w)))
      calc
        ∑ z : S, aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
          exact hsingle
        _ = aS w * 1 := by
          exact congrArg (fun u : ℂ => aS w * u) (if_pos rfl)
        _ = aS w := by
          exact mul_one (aS w)

/-- The Kronecker vector for a cardinal probe at one spectral sample. -/
def zetaLaplaceTransformCardinalVector
    (S : Finset ℂ) (z : S) : S → ℂ :=
  fun w : S => if w = z then 1 else 0

/-- The Kronecker vector has the expected value at each finite sample. -/
theorem zetaLaplaceTransformCardinalVector_apply
    (S : Finset ℂ) (z w : S) :
    zetaLaplaceTransformCardinalVector S z w =
      if w = z then 1 else 0 := by
  rfl

/-- Finite-sample realization of every Kronecker vector is exactly a cardinal family. -/
theorem zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z) :
    ∀ z w : S,
      Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        if w = z then 1 else 0 := by
  intro z w
  calc
    Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        zetaLaplaceTransformFiniteSample S (F z) w := by
      rfl
    _ = zetaLaplaceTransformCardinalVector S z w := by
      exact congrFun (hF z) w
    _ = if w = z then 1 else 0 := by
      exact zetaLaplaceTransformCardinalVector_apply S z w

/-- A pointwise cardinal family gives finite-sample realization of every Kronecker vector. -/
theorem zetaLaplaceTransformFiniteSample_eq_cardinalVector_of_cardinalFamily
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∀ z : S,
      zetaLaplaceTransformFiniteSample S (F z) =
        zetaLaplaceTransformCardinalVector S z := by
  intro z
  funext w
  calc
    zetaLaplaceTransformFiniteSample S (F z) w =
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) := by
      rfl
    _ = if w = z then 1 else 0 := by
      exact hF z w
    _ = zetaLaplaceTransformCardinalVector S z w := by
      exact (zetaLaplaceTransformCardinalVector_apply S z w).symm

/-- Finite-sample cardinal-vector realization is equivalent to the pointwise cardinal
matrix identity. -/
theorem zetaLaplaceTransformCardinalFamily_iff_finiteSample_eq_cardinalVector
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction) :
    (∀ z w : S,
      Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        if w = z then 1 else 0) ↔
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  exact
    ⟨zetaLaplaceTransformFiniteSample_eq_cardinalVector_of_cardinalFamily S F,
      zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector S F⟩

/-- The Kronecker cardinal vectors form the standard finite-coordinate expansion of every
finite sample vector. -/
theorem zetaLaplaceTransformCardinalVector_linearCombination
    (S : Finset ℂ) (aS : S → ℂ) :
    (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) = aS := by
  classical
  funext w
  calc
    (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) w =
        ∑ z : S, (aS z • zetaLaplaceTransformCardinalVector S z) w := by
      exact Finset.univ.sum_apply w
        (fun z : S => aS z • zetaLaplaceTransformCardinalVector S z)
    _ = ∑ z : S, aS z * (if w = z then 1 else 0) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u)
            (zetaLaplaceTransformCardinalVector_apply S z w))
    _ = aS w := by
      have hsingle :
          ∑ z in (Finset.univ : Finset S),
              aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
        exact Finset.sum_eq_single
          (a := w)
          (f := fun z : S => aS z * (if w = z then 1 else 0))
          (fun z _hz hzw =>
            have hne : w ≠ z := fun hwz => hzw hwz.symm
            calc
              aS z * (if w = z then 1 else 0) =
                  aS z * 0 := by
                exact congrArg (fun u : ℂ => aS z * u) (if_neg hne)
              _ = 0 := by
                exact mul_zero (aS z))
          (fun hw =>
            False.elim (hw (Finset.mem_univ w)))
      calc
        ∑ z : S, aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
          exact hsingle
        _ = aS w * 1 := by
          exact congrArg (fun u : ℂ => aS w * u) (if_pos rfl)
        _ = aS w := by
          exact mul_one (aS w)

/-- The empty spectral sample set has a vacuous cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFamily_empty_ownerPaleyWiener :
    ∃ F : (∅ : Finset ℂ) → ZetaAdmissibleFunction,
      ∀ z w : (∅ : Finset ℂ),
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  exact
    ⟨fun z =>
        False.elim (Finset.not_mem_empty (z : ℂ) z.property),
      fun z _w =>
        False.elim (Finset.not_mem_empty (z : ℂ) z.property)⟩

/-- Classical finite exponential-distribution separation by admissible probes.

If a finite coefficient family pairs to zero with the Laplace samples of every admissible
probe, then every coefficient is zero. This is the analytic Paley-Wiener uniqueness
theorem for compactly supported smooth/admissible probes; cardinal probes are downstream
consequences and are not used here. -/
theorem zetaLaplaceTransformFiniteExponentialDistribution_separated_by_admissibleProbes_ownerPaleyWiener
    (S : Finset ℂ) (c : S → ℂ)
    (hc :
      ∀ f : ZetaAdmissibleFunction,
        (∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z) = 0) :
    ∀ z : S, c z = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialSamples_separated_by_admissibleProbes_ownerAdmissibleProbe
      S c
      (fun f =>
        calc
          (∑ z : S,
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z) =
              ∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z := by
            exact Finset.sum_congr rfl
              (fun z _hz => rfl)
          _ = 0 := by
            exact hc f)

/-- Direct Paley-Wiener uniqueness for finite exponential/Laplace samples.

This wrapper keeps the finite-sample separation root upstream of cardinal probes. -/
theorem zetaLaplaceTransformFiniteExponentialSamples_separating_ownerPaleyWiener
    (S : Finset ℂ) (c : S → ℂ)
    (hc :
      ∀ f : ZetaAdmissibleFunction,
        (∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z) = 0) :
    ∀ z : S, c z = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialDistribution_separated_by_admissibleProbes_ownerPaleyWiener
      S c hc

/-- Analytic separation for finite exponential/Laplace samples by admissible probes.

If a finite dual combination of Laplace samples vanishes on every admissible probe, then
each coefficient against the Kronecker cardinal vector is zero. This is the
Paley-Wiener uniqueness input for finite exponential samples. -/
theorem zetaLaplaceTransformFiniteSample_dualCardinalCoefficients_eq_zero_ownerPaleyWiener
    (S : Finset ℂ)
    (Λ : (S → ℂ) →ₗ[ℂ] ℂ)
    (hΛ :
      ∀ f : ZetaAdmissibleFunction,
        Λ (zetaLaplaceTransformFiniteSample S f) = 0) :
    ∀ z : S,
      Λ (zetaLaplaceTransformCardinalVector S z) = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialSamples_separating_ownerPaleyWiener
      S
      (fun z : S => Λ (zetaLaplaceTransformCardinalVector S z))
      (fun f =>
        have hmap :
            Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) =
              ∑ z : S,
                zetaLaplaceTransformFiniteSample S f z *
                  Λ (zetaLaplaceTransformCardinalVector S z) := by
          calc
            Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) =
                ∑ z : S,
                  Λ (zetaLaplaceTransformFiniteSample S f z •
                    zetaLaplaceTransformCardinalVector S z) := by
              exact LinearMap.map_sum Λ Finset.univ
                (fun z : S =>
                  zetaLaplaceTransformFiniteSample S f z •
                    zetaLaplaceTransformCardinalVector S z)
            _ =
                ∑ z : S,
                  zetaLaplaceTransformFiniteSample S f z *
                    Λ (zetaLaplaceTransformCardinalVector S z) := by
              exact Finset.sum_congr rfl
                (fun z _hz =>
                  LinearMap.map_smul Λ
                    (zetaLaplaceTransformFiniteSample S f z)
                    (zetaLaplaceTransformCardinalVector S z))
        calc
          (∑ z : S,
              zetaLaplaceTransformFiniteSample S f z *
                Λ (zetaLaplaceTransformCardinalVector S z)) =
              Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) := by
            exact hmap.symm
          _ = Λ (zetaLaplaceTransformFiniteSample S f) := by
            exact congrArg Λ
              (zetaLaplaceTransformCardinalVector_linearCombination
                S (zetaLaplaceTransformFiniteSample S f))
          _ = 0 := by
            exact hΛ f)

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional separating-dual form: any linear functional on the finite
sample vector space that vanishes on all admissible Laplace-sample vectors is zero. -/
theorem zetaLaplaceTransformFiniteSample_dual_separating_ownerPaleyWiener
    (S : Finset ℂ)
    (Λ : (S → ℂ) →ₗ[ℂ] ℂ)
    (hΛ :
      ∀ f : ZetaAdmissibleFunction,
        Λ (zetaLaplaceTransformFiniteSample S f) = 0) :
    Λ = 0 := by
  have hcoeff :
      ∀ z : S,
        Λ (zetaLaplaceTransformCardinalVector S z) = 0 :=
    zetaLaplaceTransformFiniteSample_dualCardinalCoefficients_eq_zero_ownerPaleyWiener
      S Λ hΛ
  apply LinearMap.ext
  intro aS
  calc
    Λ aS =
        Λ (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) := by
      exact congrArg Λ
        (zetaLaplaceTransformCardinalVector_linearCombination S aS).symm
    _ =
        ∑ z : S, Λ (aS z • zetaLaplaceTransformCardinalVector S z) := by
      exact LinearMap.map_sum Λ Finset.univ
        (fun z : S => aS z • zetaLaplaceTransformCardinalVector S z)
    _ =
        ∑ z : S, aS z * Λ (zetaLaplaceTransformCardinalVector S z) := by
      exact Finset.sum_congr rfl
        (fun z _hz => LinearMap.map_smul Λ (aS z)
          (zetaLaplaceTransformCardinalVector S z))
    _ = ∑ z : S, aS z * 0 := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u) (hcoeff z))
    _ = 0 := by
      exact Finset.sum_eq_zero
        (fun z _hz => mul_zero (aS z))
    _ = (0 : (S → ℂ) →ₗ[ℂ] ℂ) aS := by
      rfl

/-- Finite-dimensional linear algebra converts dual separation of the finite
Laplace-evaluation range into surjectivity of the finite Laplace-evaluation map. -/
theorem zetaLaplaceTransformFiniteSample_surjective_of_dual_separating_ownerPaleyWiener
    (S : Finset ℂ)
    (hsep :
      ∀ Λ : (S → ℂ) →ₗ[ℂ] ℂ,
        (∀ f : ZetaAdmissibleFunction,
          Λ (zetaLaplaceTransformFiniteSample S f) = 0) →
          Λ = 0) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  have hRangeTop :
      LinearMap.range (zetaLaplaceTransformFiniteSampleLinearMap S) = ⊤ := by
    by_contra hRangeNeTop
    have hRangeProper :
        LinearMap.range (zetaLaplaceTransformFiniteSampleLinearMap S) < ⊤ :=
      lt_of_le_of_ne le_top hRangeNeTop
    rcases Submodule.exists_le_ker_of_lt_top
        (LinearMap.range (zetaLaplaceTransformFiniteSampleLinearMap S))
        hRangeProper with
      ⟨Λ, hΛne, hΛker⟩
    have hΛvanish :
        ∀ f : ZetaAdmissibleFunction,
          Λ (zetaLaplaceTransformFiniteSample S f) = 0 := by
      intro f
      exact LinearMap.mem_ker.mp
        (hΛker
          (LinearMap.mem_range.mpr
            ⟨f, rfl⟩))
    exact hΛne (hsep Λ hΛvanish)
  exact LinearMap.range_eq_top.mp hRangeTop

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional Fourier-Laplace/Paley-Wiener range input: every finite
sample vector lies in the range of the admissible Laplace-evaluation map. -/
theorem zetaLaplaceTransformFiniteSample_mem_range_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    aS ∈ Set.range (zetaLaplaceTransformFiniteSample S) := by
  exact
    zetaLaplaceTransformFiniteSample_surjective_of_dual_separating_ownerPaleyWiener
      S
      (zetaLaplaceTransformFiniteSample_dual_separating_ownerPaleyWiener S)
      aS

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional Fourier-Laplace/Paley-Wiener surjectivity theorem
deduced from the range statement. -/
theorem zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  intro aS
  exact Set.mem_range.mp
    (zetaLaplaceTransformFiniteSample_mem_range_ownerPaleyWiener S aS)

/-- Finite-dimensional Laplace-evaluation separation: each Kronecker vector lies in the
range of the admissible finite Laplace-sample map. -/
theorem zetaLaplaceTransformCardinalVector_mem_range_ownerPaleyWiener
    (S : Finset ℂ) (z : S) :
    zetaLaplaceTransformCardinalVector S z ∈
      Set.range (zetaLaplaceTransformFiniteSample S) := by
  exact zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    S (zetaLaplaceTransformCardinalVector S z)

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set.

This constructs one admissible cardinal probe with prescribed Laplace-transform values
against the whole finite sample set from finite-dimensional Laplace-evaluation
surjectivity. -/
theorem exists_zetaLaplaceTransformCardinalVector_ownerPaleyWiener
    (S : Finset ℂ) (z : S) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f =
        zetaLaplaceTransformCardinalVector S z := by
  exact Set.mem_range.mp
    (zetaLaplaceTransformCardinalVector_mem_range_ownerPaleyWiener S z)

/-- A pointwise cardinal-vector realization for every sample can be assembled into a
finite-sample cardinal family over an arbitrary finite index subset of a fixed ambient
sample set. This is constructive finite dependent choice by induction on the index
finset; no global choice operator is used. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamilyOn_of_forall_cardinalVector
    (S T : Finset ℂ) (hTS : T ⊆ S)
    (hT :
      ∀ z : T,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hTS z.property⟩) :
    ∃ F : T → ZetaAdmissibleFunction,
      ∀ z : T,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S
            ⟨(z : ℂ), hTS z.property⟩ := by
  induction T using Finset.induction_on with
  | empty =>
      exact
        ⟨fun z =>
            False.elim (Finset.not_mem_empty (z : ℂ) z.property),
          fun z =>
            False.elim (Finset.not_mem_empty (z : ℂ) z.property)⟩
  | insert a T ha ih =>
      have hTailSubset : T ⊆ S := by
        intro x hx
        exact hTS (Finset.mem_insert_of_mem hx)
      have hTailExists :
          ∀ z : T,
            ∃ f : ZetaAdmissibleFunction,
              zetaLaplaceTransformFiniteSample S f =
                zetaLaplaceTransformCardinalVector S
                  ⟨(z : ℂ), hTailSubset z.property⟩ := by
        intro z
        rcases hT ⟨(z : ℂ), Finset.mem_insert_of_mem z.property⟩ with
          ⟨f, hf⟩
        exact ⟨f, hf⟩
      rcases ih hTailSubset hTailExists with ⟨Ftail, hFtail⟩
      rcases hT ⟨a, Finset.mem_insert_self a T⟩ with ⟨fa, hfa⟩
      let restrictTail :
          ∀ z : (insert a T : Finset ℂ), (z : ℂ) ≠ a → T :=
        fun z hz =>
          ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩
      let F : (insert a T : Finset ℂ) → ZetaAdmissibleFunction :=
        fun z =>
          if hz : (z : ℂ) = a then
            fa
          else
            Ftail (restrictTail z hz)
      refine ⟨F, ?_⟩
      intro z
      by_cases hz : (z : ℂ) = a
      · have hFz :
            F z = fa := by
          unfold F
          exact dif_pos hz
        calc
          zetaLaplaceTransformFiniteSample S (F z) =
              zetaLaplaceTransformFiniteSample S fa := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                zetaLaplaceTransformFiniteSample S f)
              hFz
          _ = zetaLaplaceTransformCardinalVector S
              ⟨a, hTS (Finset.mem_insert_self a T)⟩ := by
            exact hfa
          _ = zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hTS z.property⟩ := by
            have hsub :
                (⟨a, hTS (Finset.mem_insert_self a T)⟩ : S) =
                  ⟨(z : ℂ), hTS z.property⟩ := by
              exact Subtype.ext hz.symm
            exact congrArg (fun w : S =>
              zetaLaplaceTransformCardinalVector S w) hsub
      · have hFz :
            F z = Ftail (restrictTail z hz) := by
          unfold F
          exact dif_neg hz
        calc
          zetaLaplaceTransformFiniteSample S (F z) =
              zetaLaplaceTransformFiniteSample S (Ftail (restrictTail z hz)) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                zetaLaplaceTransformFiniteSample S f)
              hFz
          _ = zetaLaplaceTransformCardinalVector S
              ⟨((restrictTail z hz) : ℂ),
                hTailSubset (restrictTail z hz).property⟩ := by
            exact hFtail (restrictTail z hz)
          _ = zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hTS z.property⟩ := by
            have hsub :
                (⟨((restrictTail z hz) : ℂ),
                  hTailSubset (restrictTail z hz).property⟩ : S) =
                    ⟨(z : ℂ), hTS z.property⟩ := by
              exact Subtype.ext rfl
            exact congrArg (fun w : S =>
              zetaLaplaceTransformCardinalVector S w) hsub

/-- A pointwise cardinal-vector realization for every sample can be assembled into a
finite-sample cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamily_of_forall_cardinalVector
    (S : Finset ℂ)
    (hS :
      ∀ z : S,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S z) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  have hSubset : S ⊆ S := by
    intro z hz
    exact hz
  have hExists :
      ∀ z : S,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hSubset z.property⟩ := by
    intro z
    exact hS z
  rcases exists_zetaLaplaceTransformCardinalFiniteSampleFamilyOn_of_forall_cardinalVector
      S S hSubset hExists with
    ⟨F, hF⟩
  exact ⟨F, hF⟩

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set, in
finite-sample vector form. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamily_nonempty_ownerPaleyWiener
    (S : Finset ℂ) (_hS : S ≠ ∅) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  exact exists_zetaLaplaceTransformCardinalFiniteSampleFamily_of_forall_cardinalVector
    S (fun z => exists_zetaLaplaceTransformCardinalVector_ownerPaleyWiener S z)

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set.

This is the pointwise matrix form of the finite-sample cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFamily_nonempty_ownerPaleyWiener
    (S : Finset ℂ) (hS : S ≠ ∅) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  rcases exists_zetaLaplaceTransformCardinalFiniteSampleFamily_nonempty_ownerPaleyWiener
      S hS with
    ⟨F, hF⟩
  exact ⟨F,
    zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector
      S F hF⟩

/-- Paley-Wiener cardinal interpolation on a finite spectral sample set. -/
theorem exists_zetaLaplaceTransformCardinalFamily_ownerPaleyWiener
    (S : Finset ℂ) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  by_cases hS : S = ∅
  · subst S
    exact exists_zetaLaplaceTransformCardinalFamily_empty_ownerPaleyWiener
  · exact exists_zetaLaplaceTransformCardinalFamily_nonempty_ownerPaleyWiener S hS

/-- Finite Paley-Wiener interpolation in finite-vector form.

This is the constructive basis/interpolant owner theorem: every target vector on a finite
spectral sample set is realized by the finite Laplace-transform sample vector of an
admissible function. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  exact zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    S aS

/-- Finite Paley-Wiener interpolation says the finite Laplace-sample map is surjective. -/
theorem zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  exact zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener S

/-- Finite Paley-Wiener interpolation for admissible Laplace transforms on a finite
spectral sample set.

This is the interpolation counterpart to the vertical-strip Paley-Wiener decay theorem:
compactly supported smooth admissible sources can realize arbitrary prescribed Laplace
transform values on a finite set of spectral parameters. -/
theorem exists_zetaLaplaceTransform_sample_on_finset_ownerPaleyWiener
    (S : Finset ℂ) (a : ℂ → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z = a z := by
  rcases zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
      S (zetaLaplaceTransformFiniteTarget S a) with
    ⟨f, hf⟩
  exact ⟨f, fun z hz =>
    congrFun hf ⟨z, hz⟩⟩

end ZetaAdmissibleFunction

end LFunctions
end Boundary
