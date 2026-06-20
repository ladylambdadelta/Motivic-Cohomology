import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.FiniteExponentialDetector.Owner

/-!
# Paley-Wiener finite sample interpolation

This file owns the finite Laplace-sample map, Kronecker cardinal vectors, dual
separation, and finite Paley-Wiener interpolation wrappers. It is copy-first
extracted from the current Paley-Wiener owner file, so declaration names
intentionally match the existing owner surface.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction

noncomputable section

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
  ext z
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
        (fun t : ℝ => congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
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
  ext z
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
        (fun t : ℝ => congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
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
  ext z
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
        (fun t : ℝ => congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
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
  ext w
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

/-- A cardinal family constructively realizes every finite sample vector. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_of_cardinalFamily_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ)
    (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  exact
    ⟨∑ z : S, aS z • F z,
      zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
        S aS F hF⟩

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
  ext w
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
  ext w
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

/-- Normalizing a separator makes its Laplace value at the new sample equal to one. -/
theorem zetaLaplaceTransform_normalizedSeparator_at_newSample
    (a : ℂ) (g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        a = 1 := by
  let b : ℂ := Boundary.zetaLaplaceTransform g.toZetaTestFunction' a
  calc
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        a =
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ *
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_smul S
          ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) g)
        za
    _ = b⁻¹ * b := by
      rfl
    _ = 1 := by
      exact inv_mul_cancel₀ hg

/-- Normalizing a separator preserves its zero values on the old sample set. -/
theorem zetaLaplaceTransform_normalizedSeparator_at_oldSample
    (a w : ℂ) (g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' w = 0) :
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        w = 0 := by
  calc
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        w =
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ *
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' w := by
      let S : Finset ℂ := {w}
      let zw : S := ⟨w, Finset.mem_singleton_self w⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_smul S
          ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) g)
        zw
    _ =
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ * 0 := by
      exact congrArg
        (fun u : ℂ =>
          (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ * u)
        hg
    _ = 0 := by
      exact mul_zero
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹

/-- The Lagrange update kills the new sample value of an old cardinal function. -/
theorem zetaLaplaceTransform_cardinalUpdate_vanishes_at_newSample
    (a : ℂ) (f g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    Boundary.zetaLaplaceTransform
        (f +
          (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
              (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
        a = 0 := by
  let x : ℂ := Boundary.zetaLaplaceTransform f.toZetaTestFunction' a
  let y : ℂ := Boundary.zetaLaplaceTransform g.toZetaTestFunction' a
  let c : ℂ :=
    -(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
      (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹
  calc
    Boundary.zetaLaplaceTransform
        (f + c • g).toZetaTestFunction'
        a =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' a +
          Boundary.zetaLaplaceTransform (c • g).toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add S f (c • g))
        za
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' a +
          c * Boundary.zetaLaplaceTransform g.toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' a + u)
        (congrFun (zetaLaplaceTransformFiniteSample_smul S c g) za)
    _ = x + c * y := by
      rfl
    _ = x + (-(x) * y⁻¹) * y := by
      rfl
    _ = x + -(x) * (y⁻¹ * y) := by
      exact congrArg (fun u : ℂ => x + u) (mul_assoc (-(x)) y⁻¹ y)
    _ = x + -(x) * 1 := by
      exact congrArg (fun u : ℂ => x + -(x) * u) (inv_mul_cancel₀ hg)
    _ = x + -(x) := by
      exact congrArg (fun u : ℂ => x + u) (mul_one (-(x)))
    _ = 0 := by
      exact add_neg_cancel x

/-- The Lagrange update preserves old sample values where the separator vanishes. -/
theorem zetaLaplaceTransform_cardinalUpdate_at_oldSample
    (a w : ℂ) (f g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' w = 0) :
    Boundary.zetaLaplaceTransform
        (f +
          (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
              (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
        w =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' w := by
  let c : ℂ :=
    -(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
      (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹
  calc
    Boundary.zetaLaplaceTransform
        (f + c • g).toZetaTestFunction'
        w =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' w +
          Boundary.zetaLaplaceTransform (c • g).toZetaTestFunction' w := by
      let S : Finset ℂ := {w}
      let zw : S := ⟨w, Finset.mem_singleton_self w⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add S f (c • g))
        zw
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' w +
          c * Boundary.zetaLaplaceTransform g.toZetaTestFunction' w := by
      let S : Finset ℂ := {w}
      let zw : S := ⟨w, Finset.mem_singleton_self w⟩
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + u)
        (congrFun (zetaLaplaceTransformFiniteSample_smul S c g) zw)
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + c * 0 := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + c * u)
        hg
    _ = Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + 0 := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + u)
        (mul_zero c)
    _ = Boundary.zetaLaplaceTransform f.toZetaTestFunction' w := by
      exact add_zero
        (Boundary.zetaLaplaceTransform f.toZetaTestFunction' w)

/-- A normalized separator is the new cardinal row against the old sample set. -/
theorem zetaLaplaceTransform_normalizedSeparator_cardinalRow
    (T : Finset ℂ) (a : ℂ) (g : ZetaAdmissibleFunction)
    (hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0)
    (hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    (Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        a = 1) ∧
      ∀ w : T,
        Boundary.zetaLaplaceTransform
          ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
          (w : ℂ) = 0 := by
  exact
    ⟨zetaLaplaceTransform_normalizedSeparator_at_newSample a g hgNew,
      fun w =>
        zetaLaplaceTransform_normalizedSeparator_at_oldSample
          a (w : ℂ) g (hgOld w)⟩

/-- Updating an old cardinal row keeps its old finite-sample values and kills the new
sample. -/
theorem zetaLaplaceTransform_cardinalUpdate_oldRow
    (T : Finset ℂ) (a : ℂ) (z : T)
    (f g : ZetaAdmissibleFunction)
    (hf :
      ∀ w : T,
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0)
    (hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    (Boundary.zetaLaplaceTransform
        (f +
          (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
              (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
        a = 0) ∧
      ∀ w : T,
        Boundary.zetaLaplaceTransform
          (f +
            (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
                (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
          (w : ℂ) =
            if w = z then 1 else 0 := by
  exact
    ⟨zetaLaplaceTransform_cardinalUpdate_vanishes_at_newSample a f g hgNew,
      fun w =>
        calc
          Boundary.zetaLaplaceTransform
            (f +
              (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
                  (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
            (w : ℂ) =
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ) := by
            exact zetaLaplaceTransform_cardinalUpdate_at_oldSample
              a (w : ℂ) f g (hgOld w)
          _ = if w = z then 1 else 0 := by
            exact hf w⟩

/-- A cardinal family extends across one new sample once an analytic separator for the
new sample is available. -/
theorem exists_zetaLaplaceTransformCardinalFamily_insert_of_cardinalFamily_and_separator
    (T : Finset ℂ) (a : ℂ) (ha : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (g : ZetaAdmissibleFunction)
    (hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0)
    (hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    ∃ F : {z : ℂ // z ∈ insert a T} → ZetaAdmissibleFunction,
      ∀ z w : {z : ℂ // z ∈ insert a T},
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  let normalizedSeparator : ZetaAdmissibleFunction :=
    (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g
  let oldRowUpdate : T → ZetaAdmissibleFunction :=
    fun z =>
      Ftail z +
        (-(Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) *
            (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g
  let restrictOld :
      ∀ z : {z : ℂ // z ∈ insert a T}, (z : ℂ) ≠ a → T :=
    fun z hz =>
      ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩
  let F : {z : ℂ // z ∈ insert a T} → ZetaAdmissibleFunction :=
    fun z =>
      if hz : (z : ℂ) = a then
        normalizedSeparator
      else
        oldRowUpdate (restrictOld z hz)
  exact ⟨F, fun z w =>
    if hz : (z : ℂ) = a then
      have hFz :
          F z = normalizedSeparator := by
        exact dif_pos hz
      if hw : (w : ℂ) = a then
        have hzw : w = z := by
          exact Subtype.ext (hw.trans hz.symm)
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' a := by
            exact congrArg
              (fun u : ℂ =>
                Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' u)
              hw
          _ = 1 := by
            exact zetaLaplaceTransform_normalizedSeparator_at_newSample a g hgNew
          _ = if w = z then 1 else 0 := by
            exact (if_pos hzw).symm
      else
        let wOld : T := restrictOld w hw
        have hzw_ne : w ≠ z := by
          intro hzw
          exact hw ((congrArg Subtype.val hzw).trans hz)
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = 0 := by
            exact zetaLaplaceTransform_normalizedSeparator_at_oldSample
              a (w : ℂ) g (hgOld wOld)
          _ = if w = z then 1 else 0 := by
            exact (if_neg hzw_ne).symm
    else
      let zOld : T := restrictOld z hz
      have hFz :
          F z = oldRowUpdate zOld := by
        exact dif_neg hz
      if hw : (w : ℂ) = a then
        have hzw_ne : w ≠ z := by
          intro hzw
          exact hz ((congrArg Subtype.val hzw).symm.trans hw)
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' a := by
            exact congrArg
              (fun u : ℂ =>
                Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' u)
              hw
          _ = 0 := by
            exact zetaLaplaceTransform_cardinalUpdate_vanishes_at_newSample
              a (Ftail zOld) g hgNew
          _ = if w = z then 1 else 0 := by
            exact (if_neg hzw_ne).symm
      else
        let wOld : T := restrictOld w hw
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = if wOld = zOld then 1 else 0 := by
            exact
              (zetaLaplaceTransform_cardinalUpdate_oldRow
                T a zOld (Ftail zOld) g
                (fun u => hFtail zOld u) hgOld hgNew).2 wOld
          _ = if w = z then 1 else 0 := by
            if hOld : wOld = zOld then
              have hInsert : w = z := by
                have hval : (wOld : ℂ) = (zOld : ℂ) :=
                  congrArg (fun u : T => (u : ℂ)) hOld
                exact Subtype.ext hval
              calc
                (if wOld = zOld then (1 : ℂ) else 0) = 1 := by
                  exact if_pos hOld
                _ = if w = z then (1 : ℂ) else 0 := by
                  exact (if_pos hInsert).symm
            else
              have hInsert : w ≠ z := by
                intro hEq
                have hval : (wOld : ℂ) = (zOld : ℂ) :=
                  congrArg (fun u : {z : ℂ // z ∈ insert a T} => (u : ℂ)) hEq
                exact hOld (Subtype.ext hval)
              calc
                (if wOld = zOld then (1 : ℂ) else 0) = 0 := by
                  exact if_neg hOld
                _ = if w = z then (1 : ℂ) else 0 := by
                  exact (if_neg hInsert).symm⟩

/-- Subtracting the old cardinal interpolation of an admissible function kills all old
sample values. -/
theorem zetaLaplaceTransform_cardinalCorrection_vanishes_on_oldSamples
    (T : Finset ℂ) (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (h : ZetaAdmissibleFunction) :
    ∀ w : T,
      Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) •
          (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)).toZetaTestFunction'
        (w : ℂ) = 0 := by
  intro w
  let correction : ZetaAdmissibleFunction :=
    ∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z
  have hcorrection :
      zetaLaplaceTransformFiniteSample T correction =
        zetaLaplaceTransformFiniteSample T h := by
    exact zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
      T (zetaLaplaceTransformFiniteSample T h) Ftail hFtail
  calc
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) • correction).toZetaTestFunction'
        (w : ℂ) =
        zetaLaplaceTransformFiniteSample T (h + (-1 : ℂ) • correction) w := by
      rfl
    _ =
        (zetaLaplaceTransformFiniteSample T h +
          zetaLaplaceTransformFiniteSample T ((-1 : ℂ) • correction)) w := by
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add T h ((-1 : ℂ) • correction))
        w
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          zetaLaplaceTransformFiniteSample T ((-1 : ℂ) • correction) w := by
      rfl
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          ((-1 : ℂ) • zetaLaplaceTransformFiniteSample T correction) w := by
      exact congrArg
        (fun u : ℂ => zetaLaplaceTransformFiniteSample T h w + u)
        (congrFun
          (zetaLaplaceTransformFiniteSample_smul T (-1 : ℂ) correction)
          w)
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          (-1 : ℂ) * zetaLaplaceTransformFiniteSample T correction w := by
      rfl
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          (-1 : ℂ) * zetaLaplaceTransformFiniteSample T h w := by
      exact congrArg
        (fun u : ℂ =>
          zetaLaplaceTransformFiniteSample T h w + (-1 : ℂ) * u)
        (congrFun hcorrection w)
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          -(zetaLaplaceTransformFiniteSample T h w) := by
      exact congrArg
        (fun u : ℂ => zetaLaplaceTransformFiniteSample T h w + u)
        (neg_eq_neg_one_mul
          (zetaLaplaceTransformFiniteSample T h w)).symm
    _ = 0 := by
      exact add_neg_cancel (zetaLaplaceTransformFiniteSample T h w)

/-- The new-sample value of the corrected separator is the residual after subtracting
the old cardinal interpolation. -/
theorem zetaLaplaceTransform_cardinalCorrection_at_newSample
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) •
          (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)).toZetaTestFunction'
        a =
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
        (-1 : ℂ) *
          (∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
  let correction : ZetaAdmissibleFunction :=
    ∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z
  have hCorrectionAt :
      Boundary.zetaLaplaceTransform correction.toZetaTestFunction' a =
        ∑ z : T,
          zetaLaplaceTransformFiniteSample T h z *
            Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a := by
    let S : Finset ℂ := {a}
    let za : S := ⟨a, Finset.mem_singleton_self a⟩
    calc
      Boundary.zetaLaplaceTransform correction.toZetaTestFunction' a =
          zetaLaplaceTransformFiniteSample S correction za := by
        rfl
      _ =
          (∑ z : T,
            zetaLaplaceTransformFiniteSample S
              (zetaLaplaceTransformFiniteSample T h z • Ftail z)) za := by
        exact congrFun
          (zetaLaplaceTransformFiniteSample_sum
            S Finset.univ
            (fun z : T => zetaLaplaceTransformFiniteSample T h z • Ftail z))
          za
      _ =
          ∑ z : T,
            zetaLaplaceTransformFiniteSample S
              (zetaLaplaceTransformFiniteSample T h z • Ftail z) za := by
        exact Finset.univ.sum_apply za
          (fun z : T =>
            zetaLaplaceTransformFiniteSample S
              (zetaLaplaceTransformFiniteSample T h z • Ftail z))
      _ =
          ∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a := by
        exact Finset.sum_congr rfl
          (fun z _hz =>
            calc
              zetaLaplaceTransformFiniteSample S
                  (zetaLaplaceTransformFiniteSample T h z • Ftail z) za =
                  (zetaLaplaceTransformFiniteSample T h z •
                    zetaLaplaceTransformFiniteSample S (Ftail z)) za := by
                exact congrFun
                  (zetaLaplaceTransformFiniteSample_smul
                    S (zetaLaplaceTransformFiniteSample T h z) (Ftail z))
                  za
              _ =
                  zetaLaplaceTransformFiniteSample T h z *
                    zetaLaplaceTransformFiniteSample S (Ftail z) za := by
                rfl
              _ =
                  zetaLaplaceTransformFiniteSample T h z *
                    Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a := by
                rfl)
  calc
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) • correction).toZetaTestFunction'
        a =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          Boundary.zetaLaplaceTransform ((-1 : ℂ) • correction).toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add S h ((-1 : ℂ) • correction))
        za
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (-1 : ℂ) * Boundary.zetaLaplaceTransform correction.toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' a + u)
        (congrFun
          (zetaLaplaceTransformFiniteSample_smul S (-1 : ℂ) correction)
          za)
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (-1 : ℂ) *
            (∑ z : T,
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
            (-1 : ℂ) * u)
        hCorrectionAt

/-- A function whose old-cardinal correction has nonzero residual at the new sample gives
an analytic separator for that new sample. -/
theorem exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_correctedWitness
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (h : ZetaAdmissibleFunction)
    (hResidual :
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
        (-1 : ℂ) *
          (∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) ≠ 0) :
    ∃ g : ZetaAdmissibleFunction,
      (∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0) ∧
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0 := by
  let g : ZetaAdmissibleFunction :=
    h + (-1 : ℂ) •
      (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)
  have hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0 :=
    zetaLaplaceTransform_cardinalCorrection_vanishes_on_oldSamples
      T Ftail hFtail h
  have hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0 := by
    intro hzero
    exact hResidual
      ((zetaLaplaceTransform_cardinalCorrection_at_newSample
        T a Ftail h).symm.trans hzero)
  exact ⟨g, hgOld, hgNew⟩

/-- Corrected residual witnesses at every insertion step constructively build cardinal
families on all finite spectral sample sets. -/
theorem exists_zetaLaplaceTransformCardinalFamily_of_correctedWitnesses
    (hWitness :
      ∀ (T : Finset ℂ) (a : ℂ), a ∉ T →
        ∀ Ftail : T → ZetaAdmissibleFunction,
          (∀ z w : T,
            Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
              if w = z then 1 else 0) →
            ∃ h : ZetaAdmissibleFunction,
              Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
                (-1 : ℂ) *
                  (∑ z : T,
                    zetaLaplaceTransformFiniteSample T h z *
                      Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) ≠ 0) :
    ∀ S : Finset ℂ,
      ∃ F : S → ZetaAdmissibleFunction,
        ∀ z w : S,
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
            if w = z then 1 else 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      exact exists_zetaLaplaceTransformCardinalFamily_empty_ownerPaleyWiener
  | @insert a T ha ih =>
      match ih with
      | ⟨Ftail, hFtail⟩ =>
          match hWitness T a ha Ftail hFtail with
          | ⟨h, hResidual⟩ =>
              match
                  exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_correctedWitness
                    T a Ftail hFtail h hResidual with
              | ⟨g, hgOld, hgNew⟩ =>
                  exact
                    exists_zetaLaplaceTransformCardinalFamily_insert_of_cardinalFamily_and_separator
                      T a ha Ftail hFtail g hgOld hgNew

/-- The corrected residual functional attached to an old cardinal family and a new
sample. This is the finite-correspondence coefficient left after subtracting the old
cardinal interpolation from an admissible probe. -/
def zetaLaplaceTransformCorrectedResidual
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) : ℂ :=
  Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
    (-1 : ℂ) *
      (∑ z : T,
        zetaLaplaceTransformFiniteSample T h z *
          Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a)

/-- The corrected residual is exactly the new-sample value of the corrected probe. -/
theorem zetaLaplaceTransform_cardinalCorrection_at_newSample_eq_correctedResidual
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) •
          (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)).toZetaTestFunction'
        a =
      zetaLaplaceTransformCorrectedResidual T a Ftail h := by
  exact zetaLaplaceTransform_cardinalCorrection_at_newSample T a Ftail h

/-- A nonzero corrected residual is precisely the concrete witness needed for the
constructive cardinal-family insertion step. -/
theorem exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_nonzeroResidual
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (h : ZetaAdmissibleFunction)
    (hResidual :
      zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0) :
    ∃ g : ZetaAdmissibleFunction,
      (∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0) ∧
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0 := by
  exact
    exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_correctedWitness
      T a Ftail hFtail h hResidual

/-- Nonzero corrected residual witnesses at every insertion step constructively build
cardinal families on all finite spectral sample sets. -/
theorem exists_zetaLaplaceTransformCardinalFamily_of_nonzeroCorrectedResiduals
    (hWitness :
      ∀ (T : Finset ℂ) (a : ℂ), a ∉ T →
        ∀ Ftail : T → ZetaAdmissibleFunction,
          (∀ z w : T,
            Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
              if w = z then 1 else 0) →
            ∃ h : ZetaAdmissibleFunction,
              zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0) :
    ∀ S : Finset ℂ,
      ∃ F : S → ZetaAdmissibleFunction,
        ∀ z w : S,
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
            if w = z then 1 else 0 := by
  exact
    exists_zetaLaplaceTransformCardinalFamily_of_correctedWitnesses
      (fun T a ha Ftail hFtail =>
        hWitness T a ha Ftail hFtail)

/-- The coefficient on the new sample in the residual finite exponential distribution is
one. -/
def zetaLaplaceTransformCorrectedResidualCoefficient
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) : ℂ :=
  if hz : (z : ℂ) = a then
    1
  else
    -(Boundary.zetaLaplaceTransform
        (Ftail
          ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩).toZetaTestFunction'
        a)

/-- The residual coefficient at the newly inserted sample is exactly one. -/
theorem zetaLaplaceTransformCorrectedResidualCoefficient_new
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidualCoefficient
        T a Ftail ⟨a, Finset.mem_insert_self a T⟩ = 1 := by
  exact dif_pos rfl

/-- The residual coefficient at an old sample is minus the old cardinal value at the new
sample. -/
theorem zetaLaplaceTransformCorrectedResidualCoefficient_old
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) (hz : (z : ℂ) ≠ a) :
    zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z =
      -(Boundary.zetaLaplaceTransform
        (Ftail
          ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩).toZetaTestFunction'
        a) := by
  exact dif_neg hz

/-- The residual coefficient family is explicitly nonzero at the newly inserted sample. -/
theorem zetaLaplaceTransformCorrectedResidualCoefficient_nonzero
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidualCoefficient
        T a Ftail ⟨a, Finset.mem_insert_self a T⟩ ≠ 0 := by
  intro honeZero
  have hone :
      (1 : ℂ) = 0 := by
    exact
      (zetaLaplaceTransformCorrectedResidualCoefficient_new
        T a Ftail).symm.trans honeZero
  exact one_ne_zero hone

/-- The same corrected-residual coefficient written on the ambient spectral plane.
It is supported on `insert a T`, equals one at the new sample, and equals minus the old
cardinal row evaluated at the new sample on the old support. -/
def zetaLaplaceTransformCorrectedResidualAmbientCoefficient
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : ℂ) : ℂ :=
  if hz : z = a then
    1
  else
    if hT : z ∈ T then
      -(Boundary.zetaLaplaceTransform
        (Ftail ⟨z, hT⟩).toZetaTestFunction' a)
    else
      0

/-- The ambient residual coefficient at the newly inserted sample is one. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_new
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail a = 1 := by
  exact dif_pos rfl

/-- The ambient residual coefficient at an old sample is minus the old cardinal value at
the new sample. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_old
    (T : Finset ℂ) (a z : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hzT : z ∈ T) (hza : z ≠ a) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z =
      -(Boundary.zetaLaplaceTransform
        (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
  calc
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z =
        if hT : z ∈ T then
          -(Boundary.zetaLaplaceTransform
            (Ftail ⟨z, hT⟩).toZetaTestFunction' a)
        else
          0 := by
      exact dif_neg hza
    _ =
        -(Boundary.zetaLaplaceTransform
          (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
      exact dif_pos hzT

/-- The ambient residual coefficient vanishes away from the inserted finite support. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_offSupport
    (T : Finset ℂ) (a z : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hza : z ≠ a) (hzT : z ∉ T) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z = 0 := by
  calc
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z =
        if hT : z ∈ T then
          -(Boundary.zetaLaplaceTransform
            (Ftail ⟨z, hT⟩).toZetaTestFunction' a)
        else
          0 := by
      exact dif_neg hza
    _ = 0 := by
      exact dif_neg hzT

/-- On the inserted support, the ambient and subtype residual coefficients agree. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_subtype
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
      zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
  if hz : (z : ℂ) = a then
    calc
      zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
          1 := by
        exact dif_pos hz
      _ = zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
        have hzSub : z = ⟨a, Finset.mem_insert_self a T⟩ := by
          exact Subtype.ext hz
        calc
          (1 : ℂ) =
              zetaLaplaceTransformCorrectedResidualCoefficient
                T a Ftail ⟨a, Finset.mem_insert_self a T⟩ := by
            exact (zetaLaplaceTransformCorrectedResidualCoefficient_new T a Ftail).symm
          _ = zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
            exact congrArg
              (fun u : {z : ℂ // z ∈ insert a T} =>
                zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail u)
              hzSub.symm
  else
    let hT : (z : ℂ) ∈ T := (Finset.mem_insert.mp z.property).resolve_left hz
    calc
      zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
          -(Boundary.zetaLaplaceTransform
            (Ftail ⟨(z : ℂ), hT⟩).toZetaTestFunction' a) := by
        exact
          zetaLaplaceTransformCorrectedResidualAmbientCoefficient_old
            T a (z : ℂ) Ftail hT hz
      _ = zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
        exact (zetaLaplaceTransformCorrectedResidualCoefficient_old
          T a Ftail z hz).symm

/-- The corrected residual is the pairing of the admissible Laplace samples with the
ambient finite exponential-distribution coefficient supported on `insert a T`. -/
theorem zetaLaplaceTransformCorrectedResidual_eq_ambientCoefficient_sum
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
      ∑ z in insert a T,
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
          zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z := by
  let coeff : ℂ → ℂ :=
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail
  have hnew :
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * coeff a =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a := by
    calc
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * coeff a =
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * 1 := by
        exact congrArg
          (fun u : ℂ =>
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * u)
          (zetaLaplaceTransformCorrectedResidualAmbientCoefficient_new T a Ftail)
      _ = Boundary.zetaLaplaceTransform h.toZetaTestFunction' a := by
        exact mul_one (Boundary.zetaLaplaceTransform h.toZetaTestFunction' a)
  have hold :
      (∑ z in T,
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) =
        (-1 : ℂ) *
          (∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
    calc
      (∑ z in T,
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) =
          ∑ z : T,
            -(zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
        exact Finset.sum_bij
          (fun z _hz => (⟨z, _hz⟩ : T))
          (fun _ _ => Finset.mem_univ _)
          (fun z₁ _ z₂ _ hsub => congrArg Subtype.val hsub)
          (fun z _hz => ⟨(z : ℂ), z.property, Subtype.ext rfl⟩)
          (fun z hzT =>
            have hza : z ≠ a := fun hza => haT (hza ▸ hzT)
            calc
              Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z =
                  Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
                    (-(Boundary.zetaLaplaceTransform
                      (Ftail ⟨z, hzT⟩).toZetaTestFunction' a)) := by
                exact congrArg
                  (fun u : ℂ =>
                    Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * u)
                  (zetaLaplaceTransformCorrectedResidualAmbientCoefficient_old
                    T a z Ftail hzT hza)
              _ =
                  -(Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
                    Boundary.zetaLaplaceTransform
                      (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
                exact mul_neg
                  (Boundary.zetaLaplaceTransform h.toZetaTestFunction' z)
                  (Boundary.zetaLaplaceTransform
                    (Ftail ⟨z, hzT⟩).toZetaTestFunction' a)
              _ =
                  -(zetaLaplaceTransformFiniteSample T h ⟨z, hzT⟩ *
                    Boundary.zetaLaplaceTransform
                      (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
                rfl)
      _ =
          (-1 : ℂ) *
            (∑ z : T,
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
        exact
          (Finset.sum_neg_distrib
            (s := (Finset.univ : Finset T))
            (f := fun z : T =>
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a)).trans
            (neg_eq_neg_one_mul
              (∑ z : T,
                zetaLaplaceTransformFiniteSample T h z *
                  Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a))
  calc
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (-1 : ℂ) *
            (∑ z : T,
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
      rfl
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (∑ z in T,
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) := by
      exact congrArg
        (fun u : ℂ => Boundary.zetaLaplaceTransform h.toZetaTestFunction' a + u)
        hold.symm
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * coeff a +
          (∑ z in T,
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) := by
      exact congrArg
        (fun u : ℂ =>
          u + ∑ z in T,
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z)
        hnew.symm
    _ =
        ∑ z in insert a T,
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z := by
      exact
        (Finset.sum_insert
          (s := T)
          (a := a)
          (f := fun z : ℂ =>
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z)
          haT).symm

/-- On the inserted support, the ambient coefficient summand is the subtype
coefficient summand. -/
theorem zetaLaplaceTransformCorrectedResidual_insertCoefficientSummand_eq_ambient
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) :
    Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) *
        zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
      zetaLaplaceTransformFiniteSample (insert a T) h z *
        zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
  calc
    Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) *
        zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) *
          zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) * u)
        (zetaLaplaceTransformCorrectedResidualAmbientCoefficient_subtype
          T a Ftail z)
    _ =
        zetaLaplaceTransformFiniteSample (insert a T) h z *
          zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
      rfl

/-- The corrected residual is the coefficient pairing over the inserted finite
sample, written with the subtype coefficient family. -/
theorem zetaLaplaceTransformCorrectedResidual_eq_insertCoefficientSum
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
      ∑ z in (insert a T).attach,
        zetaLaplaceTransformFiniteSample (insert a T) h z *
          zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
  let ambientCoeff : ℂ → ℂ :=
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail
  let ambientSummand : ℂ → ℂ :=
    fun z =>
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
        ambientCoeff z
  let subtypeSummand : {z : ℂ // z ∈ insert a T} → ℂ :=
    fun z =>
      zetaLaplaceTransformFiniteSample (insert a T) h z *
        zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z
  calc
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
        ∑ z in insert a T, ambientSummand z := by
      exact zetaLaplaceTransformCorrectedResidual_eq_ambientCoefficient_sum
        T a haT Ftail h
    _ =
        ∑ z in (insert a T).attach, subtypeSummand z := by
      exact Finset.sum_bij
        (fun z hz => (⟨z, hz⟩ : {z : ℂ // z ∈ insert a T}))
        (fun _ _ => Finset.mem_attach _ _)
        (fun z₁ _ z₂ _ hSubtype =>
          congrArg Subtype.val hSubtype)
        (fun z _hz => ⟨(z : ℂ), z.property, Subtype.ext rfl⟩)
        (fun z hz =>
          calc
            ambientSummand z =
                subtypeSummand ⟨z, hz⟩ := by
              exact
                zetaLaplaceTransformCorrectedResidual_insertCoefficientSummand_eq_ambient
                  T a Ftail h ⟨z, hz⟩
            _ = subtypeSummand ⟨z, hz⟩ := by
              rfl)

/-- A finite linear combination of scaled translates realizes the Lagrange-recombined
finite distribution pairing. -/
theorem zetaLaplaceTransformFiniteSample_scaledTranslateCombination_pairing
    (S : Finset ℂ) (coeff : S → ℂ)
    (seed : ZetaAdmissibleFunction)
    (δ : ℝ) (weights : Fin (Finset.univ : Finset S).card → ℂ) :
    let χ : S → ℂ :=
      fun z : S => zetaScaledTranslateCharacter δ (z : ℂ)
    let H : ZetaAdmissibleFunction :=
      ∑ k : Fin (Finset.univ : Finset S).card,
        weights k •
          ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed
    (∑ z : S, zetaLaplaceTransformFiniteSample S H z * coeff z) =
      ∑ k : Fin (Finset.univ : Finset S).card,
        weights k *
          (∑ z : S,
            (coeff z *
              Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                χ z ^ (k : ℕ)) := by
  intro χ H
  have hH :
      H =
        ∑ k : Fin (Finset.univ : Finset S).card,
          weights k •
            ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed := by
    rfl
  calc
    (∑ z : S, zetaLaplaceTransformFiniteSample S H z * coeff z) =
        ∑ z : S,
          zetaLaplaceTransformFiniteSample S
            (∑ k : Fin (Finset.univ : Finset S).card,
              weights k •
                ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z * coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg
            (fun u : ZetaAdmissibleFunction =>
              zetaLaplaceTransformFiniteSample S u z * coeff z)
            hH)
    _ =
        ∑ z : S,
          (∑ k : Fin (Finset.univ : Finset S).card,
            zetaLaplaceTransformFiniteSample S
              (weights k •
                ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z) *
              coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          have hsumPoint :
              zetaLaplaceTransformFiniteSample S
                  (∑ k : Fin (Finset.univ : Finset S).card,
                    weights k •
                      ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z =
                  ∑ k : Fin (Finset.univ : Finset S).card,
                    zetaLaplaceTransformFiniteSample S
                      (weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z := by
            calc
              zetaLaplaceTransformFiniteSample S
                  (∑ k : Fin (Finset.univ : Finset S).card,
                    weights k •
                      ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z =
                  (∑ k : Fin (Finset.univ : Finset S).card,
                    zetaLaplaceTransformFiniteSample S
                      (weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed)) z := by
                exact congrFun
                  (zetaLaplaceTransformFiniteSample_sum
                    S
                    (Finset.univ : Finset (Fin (Finset.univ : Finset S).card))
                    (fun k : Fin (Finset.univ : Finset S).card =>
                      weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed))
                  z
              _ =
                  ∑ k : Fin (Finset.univ : Finset S).card,
                    zetaLaplaceTransformFiniteSample S
                      (weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z := by
                exact
                  Finset.sum_apply
                    z
                    (Finset.univ : Finset (Fin (Finset.univ : Finset S).card))
                    (fun k : Fin (Finset.univ : Finset S).card =>
                      zetaLaplaceTransformFiniteSample S
                        (weights k •
                          ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed))
          congrArg
            (fun u : ℂ => u * coeff z)
            hsumPoint)
    _ =
        ∑ z : S,
          (∑ k : Fin (Finset.univ : Finset S).card,
            weights k *
              Boundary.zetaLaplaceTransform
                (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                (z : ℂ)) *
              coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg
            (fun u : ℂ => u * coeff z)
            (Finset.sum_congr rfl
              (fun k _hk =>
                congrFun
                  (zetaLaplaceTransformFiniteSample_smul
                    S
                    (weights k)
                    (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed))
                  z)))
    _ =
        ∑ z : S,
          ∑ k : Fin (Finset.univ : Finset S).card,
            (weights k *
              Boundary.zetaLaplaceTransform
                (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                (z : ℂ)) *
              coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          Finset.sum_mul
            (s := (Finset.univ : Finset (Fin (Finset.univ : Finset S).card)))
            (f := fun k : Fin (Finset.univ : Finset S).card =>
              weights k *
                Boundary.zetaLaplaceTransform
                  (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                  (z : ℂ))
            (a := coeff z))
    _ =
        ∑ k : Fin (Finset.univ : Finset S).card,
          ∑ z : S,
            (weights k *
              Boundary.zetaLaplaceTransform
                (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                (z : ℂ)) *
              coeff z := by
      exact Finset.sum_comm
    _ =
        ∑ k : Fin (Finset.univ : Finset S).card,
          ∑ z : S,
            weights k *
              ((coeff z *
                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                  χ z ^ (k : ℕ)) := by
      exact Finset.sum_congr rfl
        (fun k _hk =>
          Finset.sum_congr rfl
            (fun z _hz =>
              calc
                (weights k *
                    Boundary.zetaLaplaceTransform
                      (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                      (z : ℂ)) *
                    coeff z =
                    (weights k *
                      (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                        Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))) *
                      coeff z := by
                  exact congrArg
                    (fun u : ℂ => (weights k * u) * coeff z)
                    (Boundary.zetaLaplaceTransform_translate ((k : ℝ) * δ) seed (z : ℂ))
                _ =
                    weights k *
                      ((coeff z *
                        Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                          χ z ^ (k : ℕ)) := by
                  have hpow :
                      χ z ^ (k : ℕ) =
                        Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) :=
                    zetaScaledTranslateCharacter_pow δ (z : ℂ) (k : ℕ)
                  calc
                    (weights k *
                        (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                          Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))) *
                        coeff z =
                        weights k *
                          ((Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                            Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              coeff z) := by
                      exact mul_assoc
                        (weights k)
                        (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                          Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))
                        (coeff z)
                    _ =
                        weights k *
                          (coeff z *
                            (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ) *
                              Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))))) := by
                      exact congrArg
                        (fun u : ℂ => weights k * u)
                        (calc
                          (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                              Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              coeff z =
                              coeff z *
                                (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                                  Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) := by
                            exact mul_comm
                              (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))
                              (coeff z)
                          _ =
                              coeff z *
                                (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ) *
                                  Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ)))) := by
                            exact congrArg
                              (fun u : ℂ => coeff z * u)
                              (mul_comm
                                (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))))
                                (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))))
                    _ =
                        weights k *
                          ((coeff z *
                            Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ)))) := by
                      exact congrArg
                        (fun u : ℂ => weights k * u)
                        ((mul_assoc
                            (coeff z)
                            (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))
                            (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))))).symm)
                    _ =
                        weights k *
                          ((coeff z *
                            Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              χ z ^ (k : ℕ)) := by
                      exact congrArg
                        (fun u : ℂ =>
                          weights k *
                            ((coeff z *
                              Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                                u))
                        hpow.symm))
    _ =
        ∑ k : Fin (Finset.univ : Finset S).card,
          weights k *
            (∑ z : S,
              (coeff z *
                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                  χ z ^ (k : ℕ)) := by
      exact Finset.sum_congr rfl
        (fun k _hk =>
          (Finset.mul_sum Finset.univ
            (fun z : S =>
              (coeff z *
                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                  χ z ^ (k : ℕ))
            (weights k)).symm)

/-- If the residual coefficient has a seed whose Laplace value is nonzero at the
insertion point, finite Lagrange recombination of scaled translates detects the
corrected residual. -/
theorem exists_zetaLaplaceTransformCorrectedResidual_nonzero_of_seed_ownerPaleyWiener
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (seed : ZetaAdmissibleFunction)
    (hseed :
      Boundary.zetaLaplaceTransform seed.toZetaTestFunction' a ≠ 0) :
    ∃ h : ZetaAdmissibleFunction,
      zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0 := by
  let S : Finset ℂ := insert a T
  let coeff : S → ℂ :=
    zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail
  let anew : S := ⟨a, Finset.mem_insert_self a T⟩
  let support : Finset S := Finset.univ
  let sample : S → ℂ := fun z : S => (z : ℂ)
  let δ : ℝ := zetaFiniteImaginaryDifferenceScaleFinset support sample
  let χ : S → ℂ := fun z : S => zetaScaledTranslateCharacter δ (z : ℂ)
  let seededCoeff : S → ℂ :=
    fun z : S =>
      coeff z * Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)
  have hsample :
      Set.InjOn sample (support : Set S) := by
    intro z _hz w _hw hzw
    exact Subtype.ext hzw
  have hχ :
      Set.InjOn χ (support : Set S) :=
    zetaScaledTranslateCharacter_injOn_finiteSmallScale_finset
      (s := support)
      (sample := sample)
      hsample
  have hanew_mem : anew ∈ support :=
    Finset.mem_univ anew
  have hcoeff_nonzero :
      coeff anew ≠ 0 :=
    zetaLaplaceTransformCorrectedResidualCoefficient_nonzero T a Ftail
  have hseed_anew :
      Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (anew : ℂ) ≠ 0 := by
    exact hseed
  have hseeded_nonzero :
      seededCoeff anew ≠ 0 := by
    exact mul_ne_zero hcoeff_nonzero hseed_anew
  match
      zetaFiniteExponentialMoments_lagrange_recombine_finset
        (s := support)
        (χ := χ)
        (seededCoeff := seededCoeff)
        hχ
        hanew_mem with
  | ⟨weights, hweights⟩ =>
      let h : ZetaAdmissibleFunction :=
        ∑ k : Fin support.card,
          weights k •
            ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed
      have hpair_value :
          (∑ z : S,
            zetaLaplaceTransformFiniteSample S h z * coeff z) =
            seededCoeff anew := by
        calc
          (∑ z : S,
              zetaLaplaceTransformFiniteSample S h z * coeff z) =
              ∑ k : Fin support.card,
                weights k *
                  (∑ z : S,
                    (coeff z *
                      Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                        χ z ^ (k : ℕ)) := by
            exact
              zetaLaplaceTransformFiniteSample_scaledTranslateCombination_pairing
                S coeff seed δ weights
          _ = seededCoeff anew := by
            exact hweights
      have hpair_nonzero :
          (∑ z : S,
            zetaLaplaceTransformFiniteSample S h z * coeff z) ≠ 0 := by
        intro hzero
        exact hseeded_nonzero (hpair_value.symm.trans hzero)
      exact ⟨h, fun hResidualZero =>
        hpair_nonzero
          ((zetaLaplaceTransformCorrectedResidual_eq_insertCoefficientSum
            T a haT Ftail h).symm.trans hResidualZero)⟩

/-- The residual coefficient at an insertion step is a nonzero finite exponential
distribution, hence some admissible probe has nonzero corrected residual. -/
theorem exists_zetaLaplaceTransformCorrectedResidual_nonzero_ownerPaleyWiener
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction) :
    ∃ h : ZetaAdmissibleFunction,
      zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0 := by
  match exists_zetaLaplaceTransform_nonzero_seed a with
  | ⟨seed, hseed⟩ =>
      exact
        exists_zetaLaplaceTransformCorrectedResidual_nonzero_of_seed_ownerPaleyWiener
          T a haT Ftail seed hseed

/-- Constructive finite Paley-Wiener cardinal interpolation, obtained by inserting
samples one at a time and detecting the corrected residual at each insertion step. -/
theorem exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener
    (S : Finset ℂ) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  exact
    exists_zetaLaplaceTransformCardinalFamily_of_nonzeroCorrectedResiduals
      (fun T a haT Ftail _hFtail =>
        exists_zetaLaplaceTransformCorrectedResidual_nonzero_ownerPaleyWiener
          T a haT Ftail)
      S

/-- Constructive finite Paley-Wiener interpolation in finite-vector form. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  match exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener S with
  | ⟨F, hF⟩ =>
      exact
        exists_zetaLaplaceTransformFiniteSample_eq_of_cardinalFamily_ownerPaleyWiener
          S aS F hF

/-- Finite exponential-distribution separation by admissible probes.

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
  intro z
  match exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener S with
  | ⟨F, hF⟩ =>
      have hpair :
          (∑ w : S, zetaLaplaceTransformFiniteSample S (F z) w * c w) = 0 :=
        hc (F z)
      have hsum :
          (∑ w : S, zetaLaplaceTransformFiniteSample S (F z) w * c w) = c z := by
        calc
          (∑ w : S, zetaLaplaceTransformFiniteSample S (F z) w * c w) =
              ∑ w : S, (if w = z then (1 : ℂ) else 0) * c w := by
            exact Finset.sum_congr rfl
              (fun w _hw =>
                congrArg (fun u : ℂ => u * c w) (hF z w))
          _ = c z := by
            have hsingle :
                (∑ w in (Finset.univ : Finset S),
                    (if w = z then (1 : ℂ) else 0) * c w) =
                  (if z = z then (1 : ℂ) else 0) * c z := by
              exact Finset.sum_eq_single
                (a := z)
                (f := fun w : S => (if w = z then (1 : ℂ) else 0) * c w)
                (fun w _hw hwz =>
                  calc
                    (if w = z then (1 : ℂ) else 0) * c w =
                        0 * c w := by
                      exact congrArg (fun u : ℂ => u * c w) (if_neg hwz)
                    _ = 0 := by
                      exact zero_mul (c w))
                (fun hz =>
                  False.elim (hz (Finset.mem_univ z)))
            calc
              (∑ w : S, (if w = z then (1 : ℂ) else 0) * c w) =
                  (if z = z then (1 : ℂ) else 0) * c z := by
                exact hsingle
              _ = 1 * c z := by
                exact congrArg (fun u : ℂ => u * c z) (if_pos rfl)
              _ = c z := by
                exact one_mul (c z)
      exact hsum.symm.trans hpair

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
              exact _root_.map_sum Λ
                (fun z : S =>
                  zetaLaplaceTransformFiniteSample S f z •
                    zetaLaplaceTransformCardinalVector S z)
                Finset.univ
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
  exact LinearMap.ext
    (fun aS =>
      calc
        Λ aS =
            Λ (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) := by
          exact congrArg Λ
            (zetaLaplaceTransformCardinalVector_linearCombination S aS).symm
        _ =
            ∑ z : S, Λ (aS z • zetaLaplaceTransformCardinalVector S z) := by
          exact _root_.map_sum Λ
            (fun z : S => aS z • zetaLaplaceTransformCardinalVector S z)
            Finset.univ
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
          rfl)

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
  intro aS
  exact exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener S aS

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
  exact
    exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener
      S (zetaLaplaceTransformCardinalVector S z)

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
  | @insert a T ha ih =>
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
        match hT ⟨(z : ℂ), Finset.mem_insert_of_mem z.property⟩ with
        | ⟨f, hf⟩ =>
            have hsub :
                (⟨(z : ℂ), hTS (Finset.mem_insert_of_mem z.property)⟩ : S) =
                  ⟨(z : ℂ), hTailSubset z.property⟩ := by
              exact Subtype.ext rfl
            exact
              ⟨f,
                hf.trans
                  (congrArg
                    (fun w : S => zetaLaplaceTransformCardinalVector S w)
                    hsub)⟩
      match ih hTailSubset hTailExists with
      | ⟨Ftail, hFtail⟩ =>
          match hT ⟨a, Finset.mem_insert_self a T⟩ with
          | ⟨fa, hfa⟩ =>
              let restrictTail :
                  ∀ z : {z : ℂ // z ∈ insert a T}, (z : ℂ) ≠ a → T :=
                fun z hz =>
                  ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩
              let F : {z : ℂ // z ∈ insert a T} → ZetaAdmissibleFunction :=
                fun z =>
                  if hz : (z : ℂ) = a then
                    fa
                  else
                    Ftail (restrictTail z hz)
              exact ⟨F, fun z =>
                if hz : (z : ℂ) = a then
                    have hFz :
                        F z = fa := by
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
                else
                    have hFz :
                        F z = Ftail (restrictTail z hz) := by
                      exact dif_neg hz
                    calc
                      zetaLaplaceTransformFiniteSample S (F z) =
                          zetaLaplaceTransformFiniteSample S
                            (Ftail (restrictTail z hz)) := by
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
                          zetaLaplaceTransformCardinalVector S w) hsub⟩

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
  match
      exists_zetaLaplaceTransformCardinalFiniteSampleFamilyOn_of_forall_cardinalVector
        S S hSubset hExists with
  | ⟨F, hF⟩ => exact ⟨F, hF⟩

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
  match
      exists_zetaLaplaceTransformCardinalFiniteSampleFamily_nonempty_ownerPaleyWiener
        S hS with
  | ⟨F, hF⟩ =>
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
  exact exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener S

/-- Finite Paley-Wiener interpolation in finite-vector form.

This is the constructive basis/interpolant owner theorem: every target vector on a finite
spectral sample set is realized by the finite Laplace-transform sample vector of an
admissible function. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  exact
    exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener S aS

/-- Finite Paley-Wiener interpolation says the finite Laplace-sample map is surjective. -/
theorem zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  intro aS
  exact exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener S aS

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
  match
      zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
        S (zetaLaplaceTransformFiniteTarget S a) with
  | ⟨f, hf⟩ =>
      exact ⟨f, fun z hz =>
        congrFun hf ⟨z, hz⟩⟩

end

end ZetaAdmissibleFunction

end LFunctions
end Boundary
