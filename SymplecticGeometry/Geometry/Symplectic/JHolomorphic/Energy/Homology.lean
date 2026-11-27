/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Energy.Surface
public import SymplecticGeometry.Geometry.Symplectic.JHolomorphic.Energy.Density
public import TauCeti.Geometry.Manifold.SmoothSingular.Period
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
import SymplecticGeometry.Geometry.Manifold.DeRham.FundamentalClass
import SymplecticGeometry.Geometry.Symplectic.JHolomorphic.Energy.Surface

/-!
# The energy of pseudoholomorphic curves is topological

Let `(C, j)` be a closed almost complex surface, oriented by `o` so that the frames `(e, j e)` are
positive, and let `M` carry a two-form `ω` (`form` in the code) and an almost complex structure
`J`. A smooth map `u : C → M` represents the class `A = u_* [C]` of the integral singular homology
`H₂(M; ℤ)`, where `[C]` is the fundamental class of the homological orientation of `-o` (Tau Ceti's
homological orientation of `o` has the opposite sign to the classes of positively oriented
simplices; see `TauCeti.Manifold.Orientation.integralTopForm_eq_closedFormHomologyPeriod`).

For closed `ω` the integral `∫_C u^* ω` depends only on `A`: it is the period `⟨[ω], A⟩`, Tau
Ceti's `TauCeti.closedFormHomologyPeriod` on `A` read with coefficients `ℤ` through
`TauCeti.uliftIntHomologyIso`
(`TauCeti.Manifold.Orientation.integralTopForm_mpullback_eq_closedFormHomologyPeriod`). Since the
energy of a pseudoholomorphic map is `∫_C u^* ω`, it follows that such maps have energy
`⟨[ω], A⟩`; for a compatible pair they minimize the energy among smooth maps representing `A`
(by the Wirtinger inequality `∫_C v^* ω ≤ E(v)`), and under tameness `⟨[ω], A⟩ > 0` unless `u` is
locally constant.

## Main results

* `TauCeti.SmoothTwoForm.energy_eq_closedFormHomologyPeriod`: a pseudoholomorphic `u` representing
  `A` has energy `⟨[ω], A⟩`.
* `TauCeti.SmoothTwoForm.Compatible.energy_le_energy`: for a compatible pair, a pseudoholomorphic
  map has the least energy among the smooth maps representing the same class.
* `TauCeti.SmoothTwoForm.Tames.closedFormHomologyPeriod_pos`: under tameness, a pseudoholomorphic
  map that is not locally constant represents a class on which `[ω]` is positive.
* `TauCeti.SmoothTwoForm.Compatible.energy_identity_and_homology`: the energy identity of
  `TauCeti.SmoothTwoForm.Compatible.energy_identity` together with the three statements above,
  with the energy written as `½ ∫_C |du|² dvol`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.5,
  equation (4.5.4) and the paragraph after it.
* [C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*][Wendl2010],
  Definition 2.18 and Proposition 2.19.
-/

public section

open AlgebraicTopology CategoryTheory Module
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

namespace SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {C : Type} [TopologicalSpace C] [ChartedSpace E' C] [IsManifold 𝓘(ℝ, E') ∞ C]
  [T2Space C] [CompactSpace C]
  {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {j : SmoothAlmostComplexStructure 𝓘(ℝ, E') C} {u : C → M}
  (hE' : finrank ℝ E' = 2) {o : Manifold.Orientation 𝓘(ℝ, E') C (Fin 2)}
  {A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M)}

/-- **The energy of a pseudoholomorphic curve is topological.** For a closed two-form `ω` and a
smooth pseudoholomorphic map `u` from a closed surface `C`, oriented by `o`, that represents
`A ∈ H₂(M; ℤ)`, the energy of `u` is `⟨[ω], A⟩`. -/
theorem energy_eq_closedFormHomologyPeriod (hform : form ∈ closedForms I M 2)
    (hu : ContMDiff 𝓘(ℝ, E') I ∞ u)
    (hA : ((-o).toHomologicalOrientation hE').mapFundamentalClass hE' ⟨u, hu.continuous⟩ = A)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) :
    form.energy J j o u =
      closedFormHomologyPeriod ⟨form, hform⟩
        ((uliftIntHomologyIso (TopCat.of M) 2).hom.hom A) := by
  rw [energy_eq_integralTopForm_mpullback hhol, ← hA]
  exact o.integralTopForm_mpullback_eq_closedFormHomologyPeriod hE' ⟨form, hform⟩ hu

/-- **Pseudoholomorphic curves minimize the energy in their class.** Let `ω` be closed and
compatible with `J`, and orient the closed surface `C` by `o` so that the frames `(e, j e)` are
positive. If `u` is smooth and pseudoholomorphic and `v` is any smooth map representing the same
class `A ∈ H₂(M; ℤ)` as `u`, then `E(u) ≤ E(v)`. -/
theorem Compatible.energy_le_energy (hc : form.Compatible J) (hform : form ∈ closedForms I M 2)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, E') c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff 𝓘(ℝ, E') I ∞ u)
    (hA : ((-o).toHomologicalOrientation hE').mapFundamentalClass hE' ⟨u, hu.continuous⟩ = A)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {v : C → M} (hv : ContMDiff 𝓘(ℝ, E') I ∞ v)
    (hvA : ((-o).toHomologicalOrientation hE').mapFundamentalClass hE' ⟨v, hv.continuous⟩ = A) :
    form.energy J j o u ≤ form.energy J j o v := by
  rw [energy_eq_closedFormHomologyPeriod hE' hform hu hA hhol,
    ← hvA, ← o.integralTopForm_mpullback_eq_closedFormHomologyPeriod hE' ⟨form, hform⟩ hv]
  exact hc.integralTopForm_mpullback_le_energy ho (hv.of_le (by simp))

/-- **Positivity of the class of a nonconstant pseudoholomorphic curve.** Let `ω` be closed and
tame `J`, and orient the closed surface `C` by `o` so that the frames `(e, j e)` are positive. If
a smooth pseudoholomorphic map `u` represents `A ∈ H₂(M; ℤ)` and is not locally constant, then
`⟨[ω], A⟩ > 0`. -/
theorem Tames.closedFormHomologyPeriod_pos (htame : form.Tames J)
    (hform : form ∈ closedForms I M 2)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, E') c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff 𝓘(ℝ, E') I ∞ u)
    (hA : ((-o).toHomologicalOrientation hE').mapFundamentalClass hE' ⟨u, hu.continuous⟩ = A)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) (hlc : ¬IsLocallyConstant u) :
    0 < closedFormHomologyPeriod ⟨form, hform⟩
      ((uliftIntHomologyIso (TopCat.of M) 2).hom.hom A) := by
  rw [← energy_eq_closedFormHomologyPeriod hE' hform hu hA hhol]
  refine (htame.energy_nonneg ho).lt_of_ne fun h ↦ hlc ?_
  exact (htame.energy_eq_zero_iff_isLocallyConstant ho (hu.of_le (by simp))).1 h.symm

/-- **The energy identity for pseudoholomorphic curves.** Let `ω` be compatible with `J`, let the
closed surface `C` be oriented by `o` so that the frames `(e, j e)` are positive, let `dvol` be an
area form taming `j`, and let `u : C → M` be smooth. Write `E(u) = ½ ∫_C |du|² dvol`, with `|·|²`
the squared norm for the metrics `dvol (·, j ·)` and `ω (·, J ·)`. Then
* `E(u) = ∫_C |∂̄_J u|² dvol + ∫_C u^* ω`, with `∂̄_J u = ½ (du + J ∘ du ∘ j)`;
* if `u` is pseudoholomorphic, `E(u) = ∫_C u^* ω`;
* `E(u)` is the same for every area form taming `j`;
* if `ω` is closed and `u` is pseudoholomorphic and represents `A ∈ H₂(M; ℤ)`, then
  `E(u) = ⟨[ω], A⟩`, `E(u) ≤ E(v)` for every smooth `v` representing `A`, and `⟨[ω], A⟩ > 0`
  unless `u` is locally constant.

Here `u` represents `A` when `A` is the image under `u` of the fundamental class of the
homological orientation of `-o`, which is the class whose local orientations are those of
positively oriented simplices. In the metric of the compatible pair, `|du|²` is the sum of the
squared lengths of `du e` and `du (j e)` for `e` of unit length for `dvol (·, j ·)`
(`TauCeti.SmoothTwoForm.Compatible.normSq_eq_inner`).

Milestone: *Energy identity for J-holomorphic curves*. -/
theorem Compatible.energy_identity_and_homology (hc : form.Compatible J)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, E') c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    {dvol : SmoothTwoForm 𝓘(ℝ, E') C} (hdvol : dvol.Tames j) (hu : ContMDiff 𝓘(ℝ, E') I ∞ u) :
    (1 / 2 * integralTopForm o
        (fun c ↦ form.normSq J j dvol (mfderiv 𝓘(ℝ, E') I u c).toLinearMap • dvol.val c) =
      integralTopForm o (fun c ↦ form.normSq J j dvol (complexAntilinearPart
          (j.toEndomorphism c : TangentSpace 𝓘(ℝ, E') c →ₗ[ℝ] TangentSpace 𝓘(ℝ, E') c)
          (J.toEndomorphism (u c) : TangentSpace I (u c) →ₗ[ℝ] TangentSpace I (u c))
          (mfderiv 𝓘(ℝ, E') I u c).toLinearMap) • dvol.val c) +
        integralTopForm o (mpullback 𝓘(ℝ, E') I u form.val)) ∧
    ((∀ c, IsPseudoholomorphicAt j J u c) →
      1 / 2 * integralTopForm o
          (fun c ↦ form.normSq J j dvol (mfderiv 𝓘(ℝ, E') I u c).toLinearMap • dvol.val c) =
        integralTopForm o (mpullback 𝓘(ℝ, E') I u form.val)) ∧
    (∀ dvol' : SmoothTwoForm 𝓘(ℝ, E') C, dvol'.Tames j →
      1 / 2 * integralTopForm o
          (fun c ↦ form.normSq J j dvol' (mfderiv 𝓘(ℝ, E') I u c).toLinearMap • dvol'.val c) =
        1 / 2 * integralTopForm o
          (fun c ↦ form.normSq J j dvol (mfderiv 𝓘(ℝ, E') I u c).toLinearMap • dvol.val c)) ∧
    ∀ hform : form ∈ closedForms I M 2,
      ((-o).toHomologicalOrientation hE').mapFundamentalClass hE' ⟨u, hu.continuous⟩ = A →
      (∀ c, IsPseudoholomorphicAt j J u c) →
      (1 / 2 * integralTopForm o
          (fun c ↦ form.normSq J j dvol (mfderiv 𝓘(ℝ, E') I u c).toLinearMap • dvol.val c) =
        closedFormHomologyPeriod ⟨form, hform⟩
          ((uliftIntHomologyIso (TopCat.of M) 2).hom.hom A)) ∧
      (∀ v : C → M, ∀ hv : ContMDiff 𝓘(ℝ, E') I ∞ v,
        ((-o).toHomologicalOrientation hE').mapFundamentalClass hE' ⟨v, hv.continuous⟩ = A →
        1 / 2 * integralTopForm o
            (fun c ↦ form.normSq J j dvol (mfderiv 𝓘(ℝ, E') I u c).toLinearMap • dvol.val c) ≤
          1 / 2 * integralTopForm o
            (fun c ↦ form.normSq J j dvol (mfderiv 𝓘(ℝ, E') I v c).toLinearMap • dvol.val c)) ∧
      (¬IsLocallyConstant u →
        0 < closedFormHomologyPeriod ⟨form, hform⟩
          ((uliftIntHomologyIso (TopCat.of M) 2).hom.hom A)) := by
  obtain ⟨h₁, h₂, h₃⟩ := hc.energy_identity hdvol (hu.of_le (by simp))
  refine ⟨h₁, h₂, h₃, fun hform hA hhol ↦ ?_⟩
  simp only [← energy_eq_half_integralTopForm_normSq hdvol]
  exact ⟨energy_eq_closedFormHomologyPeriod hE' hform hu hA hhol,
    fun _ hv hvA ↦ hc.energy_le_energy hE' hform ho hu hA hhol hv hvA,
    hc.tames.closedFormHomologyPeriod_pos hE' hform ho hu hA hhol⟩

end SmoothTwoForm

end TauCeti

end
