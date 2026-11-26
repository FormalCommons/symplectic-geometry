/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Geometry.Manifold.Morse.ScalarComposition

/-!
# Weinstein cobordisms

Let `(ω, X, f)` be a Weinstein structure on a boundaryless manifold `M`, and `a < b` two regular
values of `f`. The *Weinstein cobordism* between the levels `a` and `b` is the region
`f ⁻¹' Icc a b`, with lower boundary `f ⁻¹' {a}` and upper boundary `f ⁻¹' {b}`, together with
the restriction of `(ω, X, f)` to it. It is compact, it contains finitely many critical points of
`f`, none of them on its boundary, and `X` enters it along the lower level and leaves it along the
upper one. The cobordism is *elementary* when all critical points of `f` in the region lie on one
level `f ⁻¹' {c}` with `a < c < b` (or there are none).

## Main declarations

* `SymplecticGeometry.IsWeinsteinCobordism ω X f a b`: `(ω, X, f)` is a Weinstein structure,
  `a < b`, and `a` and `b` are regular values of `f`; with
  `SymplecticGeometry.isWeinsteinCobordism_iff`.
* `SymplecticGeometry.IsWeinsteinCobordism.isCompact` and `.compactSpace`: the region
  `f ⁻¹' Icc a b` is compact.
* `SymplecticGeometry.IsWeinsteinCobordism.finite_criticalPoints` and
  `.criticalPoints_inter_subset_preimage_Ioo`: the region contains finitely many critical points,
  all in the open region `f ⁻¹' Ioo a b`.
* `SymplecticGeometry.IsWeinsteinCobordism.mvfderiv_apply_pos_of_eq_lower` and
  `.mvfderiv_apply_pos_of_eq_upper`: `0 < df(X)` along both boundary levels, so that `X` points
  into the region along the lower level and out of it along the upper level.
* `SymplecticGeometry.IsWeinsteinCobordism.comp` and `.pullback`: reparametrizing `f` by a
  strictly increasing `h` moves the levels to `h a` and `h b`; a diffeomorphism pulls a Weinstein
  cobordism back to one between the same levels.
* `SymplecticGeometry.IsElementaryWeinsteinCobordism`: a Weinstein cobordism whose critical
  points in the region lie on one level strictly between `a` and `b`; with
  `SymplecticGeometry.IsWeinsteinCobordism.isElementary_iff` (the critical values in the region
  form a subsingleton) and `.isElementary_of_criticalPoints_inter_eq_empty`, and stable under
  `.comp` and `.pullback`.
* `SymplecticGeometry.isElementaryWeinsteinCobordism_norm_sq`: for the radial Weinstein structure
  on a symplectic vector space, such as `ℂⁿ`, every region between two nonzero levels of
  `‖x‖ ^ 2` is an elementary Weinstein cobordism.

## Implementation notes

Cieliebak and Eliashberg define a Weinstein cobordism as a compact manifold with boundary
`W = ∂₋W ⊔ ∂₊W` with a Weinstein structure whose function has `∂₋W` and `∂₊W` as its minimum and
maximum regular levels. Here the cobordism is instead the region between two regular levels of a
Weinstein structure on a boundaryless manifold, so that later statements stay on boundaryless
manifolds. The predicate is on `(ω, X, f, a, b)`; the region is `f ⁻¹' Icc a b`, and the
predicate needs no definition of its own for it.

This describes only the cobordisms of Cieliebak and Eliashberg that are cut out of a Weinstein
manifold. Since `f` is proper and bounded below, the lower boundary `f ⁻¹' {a}` then bounds the
Weinstein domain `{f ≤ a}` when `M` has positive dimension
(`SymplecticGeometry.IsWeinsteinStructure.isWeinsteinDomain_scalarRegularSublevel`). A cobordism
whose lower boundary bounds no Weinstein domain, such as `[0, 1] × S³` in the symplectization of
an overtwisted contact sphere, is not of this form.

Cieliebak and Eliashberg call a cobordism elementary when no trajectory of `X` joins two critical
points; the condition used here, that all critical points lie on one level, implies it, since `f`
increases strictly along the nonconstant trajectories of a gradient-like field
(`TauCeti.IsGradientLike.strictMono_comp`). It is the form in which elementary cobordisms are
used for handle attachment.

The critical points of `h ∘ f` for a reparametrization with `h' > 0` are those of `f`
(`TauCeti.mem_criticalPoints_scalar_comp_iff`, `TauCeti.IsRegularValue.scalar_comp`), and a
diffeomorphism preserves regular values
(`Diffeomorph.isRegularValue_comp_iff`).

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Section 11.1
-/

public section

open Set TauCeti TauCeti.Manifold
open scoped Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]

/-- A **Weinstein cobordism** between the levels `a` and `b`: `(ω, X, f)` is a Weinstein
structure, `a < b`, and `a` and `b` are regular values of `f`. The cobordism is the region
`f ⁻¹' Icc a b`, whose boundary consists of the lower level `f ⁻¹' {a}` and the upper level
`f ⁻¹' {b}`.

The predicate describes only cobordisms cut out of a Weinstein manifold, whose lower boundary
bounds the Weinstein domain `{f ≤ a}`; it does not cover a general Weinstein cobordism, a
compact manifold with boundary whose lower boundary need bound no Weinstein domain. -/
structure IsWeinsteinCobordism (ω : SmoothTwoForm 𝓘(ℝ, E) M)
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : M → ℝ) (a b : ℝ) : Prop where
  /-- The triple is a Weinstein structure. -/
  isWeinsteinStructure : IsWeinsteinStructure ω X f
  /-- The lower level is below the upper level. -/
  lt : a < b
  /-- The lower level is a regular value. -/
  isRegularValue_lower : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a
  /-- The upper level is a regular value. -/
  isRegularValue_upper : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b

variable {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
  {a b : ℝ}

/-- The conditions of `SymplecticGeometry.IsWeinsteinCobordism`, as a conjunction. -/
theorem isWeinsteinCobordism_iff :
    IsWeinsteinCobordism ω X f a b ↔
      IsWeinsteinStructure ω X f ∧ a < b ∧ IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a ∧
        IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b :=
  ⟨fun h ↦ ⟨h.isWeinsteinStructure, h.lt, h.isRegularValue_lower, h.isRegularValue_upper⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

namespace IsWeinsteinCobordism

/-- The region `f ⁻¹' Icc a b` of a Weinstein cobordism is compact. -/
theorem isCompact (h : IsWeinsteinCobordism ω X f a b) : IsCompact (f ⁻¹' Icc a b) :=
  h.isWeinsteinStructure.isProperMap.isCompact_preimage isCompact_Icc

/-- The region `f ⁻¹' Icc a b` of a Weinstein cobordism is a compact space. -/
theorem compactSpace (h : IsWeinsteinCobordism ω X f a b) : CompactSpace (f ⁻¹' Icc a b) :=
  isCompact_iff_compactSpace.1 h.isCompact

/-- The region of a Weinstein cobordism contains only finitely many critical points of `f`. -/
theorem finite_criticalPoints (h : IsWeinsteinCobordism ω X f a b) :
    (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b).Finite :=
  h.isWeinsteinStructure.isGeneralizedMorse.finite_criticalPoints_inter h.isCompact

/-- The critical points of `f` in the region of a Weinstein cobordism lie in the open region
`f ⁻¹' Ioo a b`: none lies on the two boundary levels. -/
theorem criticalPoints_inter_subset_preimage_Ioo (h : IsWeinsteinCobordism ω X f a b) :
    criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b ⊆ f ⁻¹' Ioo a b := by
  intro x hx
  have hl : x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b := by
    rwa [criticalPoints_inter_preimage_Ioc_eq_Icc h.isRegularValue_lower]
  have hu : x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a b := by
    rwa [criticalPoints_inter_preimage_Ico_eq_Icc h.isRegularValue_upper]
  exact ⟨hl.2.1, hu.2.2⟩

/-- Along the lower level `f ⁻¹' {a}` of a Weinstein cobordism, the field increases `f`: it points
into the region. -/
theorem mvfderiv_apply_pos_of_eq_lower (h : IsWeinsteinCobordism ω X f a b) {x : M}
    (hx : f x = a) : 0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
  h.isWeinsteinStructure.isGradientLike.mvfderiv_apply_pos
    (isRegularPoint_iff_mvfderiv_ne_zero.1 (h.isRegularValue_lower.isRegularPoint hx))

/-- Along the upper level `f ⁻¹' {b}` of a Weinstein cobordism, the field increases `f`: it points
out of the region. -/
theorem mvfderiv_apply_pos_of_eq_upper (h : IsWeinsteinCobordism ω X f a b) {x : M}
    (hx : f x = b) : 0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
  h.isWeinsteinStructure.isGradientLike.mvfderiv_apply_pos
    (isRegularPoint_iff_mvfderiv_ne_zero.1 (h.isRegularValue_upper.isRegularPoint hx))

/-- Reparametrizing the function of a Weinstein cobordism between `a` and `b` by a smooth strictly
increasing `h` with `h' > 0` at every value of `f` gives a Weinstein cobordism between `h a` and
`h b`, as long as `h ∘ f` is proper and bounded below. -/
theorem comp (hW : IsWeinsteinCobordism ω X f a b) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmono : StrictMono h) (hpos : ∀ x, 0 < deriv h (f x)) (hp : IsProperMap (h ∘ f))
    (hb : BddBelow (range (h ∘ f))) : IsWeinsteinCobordism ω X (h ∘ f) (h a) (h b) := by
  have hf := hW.isWeinsteinStructure.isGeneralizedMorse.contMDiff.mdifferentiable (by simp)
  exact ⟨hW.isWeinsteinStructure.comp hh hpos hp hb, hmono hW.lt,
    hW.isRegularValue_lower.scalar_comp hf hmono.injective fun x ↦ (hpos x).ne',
    hW.isRegularValue_upper.scalar_comp hf hmono.injective fun x ↦ (hpos x).ne'⟩

/-- **Weinstein cobordisms pull back along diffeomorphisms.** If `(ω, X, f)` is a Weinstein
cobordism between `a` and `b` on `M` and `Φ : M' → M` is a diffeomorphism, then
`(Φ^* ω, Φ^* X, f ∘ Φ)` is a Weinstein cobordism between the same levels, whose region
`(f ∘ Φ) ⁻¹' Icc a b` is the preimage under `Φ` of that of `f`. -/
theorem pullback (hW : IsWeinsteinCobordism ω X f a b) {M' : Type*} [TopologicalSpace M']
    [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M']
    (Φ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M' M (⊤ : ℕ∞)) :
    IsWeinsteinCobordism (SmoothForm.mpullback Φ Φ.contMDiff ω)
      (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ X) (f ∘ Φ) a b :=
  ⟨hW.isWeinsteinStructure.pullback Φ, hW.lt,
    (Φ.isRegularValue_comp_iff (by simp)).2 hW.isRegularValue_lower,
    (Φ.isRegularValue_comp_iff (by simp)).2 hW.isRegularValue_upper⟩

end IsWeinsteinCobordism

/-! ### Elementary cobordisms -/

/-- An **elementary Weinstein cobordism** between the levels `a` and `b`: a Weinstein cobordism
whose critical points in the region `f ⁻¹' Icc a b` all lie on one level `f ⁻¹' {c}` with
`a < c < b`. A cobordism without critical points is elementary
(`SymplecticGeometry.IsWeinsteinCobordism.isElementary_of_criticalPoints_inter_eq_empty`). -/
structure IsElementaryWeinsteinCobordism (ω : SmoothTwoForm 𝓘(ℝ, E) M)
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : M → ℝ) (a b : ℝ) : Prop
    extends IsWeinsteinCobordism ω X f a b where
  /-- The critical points in the region lie on one level strictly between `a` and `b`. -/
  exists_criticalPoints_inter_subset :
    ∃ c ∈ Ioo a b, criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b ⊆ f ⁻¹' {c}

/-- The conditions of `SymplecticGeometry.IsElementaryWeinsteinCobordism`, as a conjunction. -/
theorem isElementaryWeinsteinCobordism_iff :
    IsElementaryWeinsteinCobordism ω X f a b ↔
      IsWeinsteinCobordism ω X f a b ∧
        ∃ c ∈ Ioo a b, criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b ⊆ f ⁻¹' {c} :=
  ⟨fun h ↦ ⟨h.toIsWeinsteinCobordism, h.exists_criticalPoints_inter_subset⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

namespace IsWeinsteinCobordism

/-- A Weinstein cobordism is elementary exactly when `f` takes at most one value at its critical
points in the region. -/
theorem isElementary_iff (h : IsWeinsteinCobordism ω X f a b) :
    IsElementaryWeinsteinCobordism ω X f a b ↔
      (f '' (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b)).Subsingleton := by
  refine ⟨fun he ↦ ?_, fun hs ↦ ⟨h, ?_⟩⟩
  · obtain ⟨c, -, hc⟩ := he.exists_criticalPoints_inter_subset
    exact subsingleton_singleton.anti (image_subset_iff.2 hc)
  · rcases (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · exact ⟨(a + b) / 2, ⟨by linarith [h.lt], by linarith [h.lt]⟩, by simp [he]⟩
    · exact ⟨f x, h.criticalPoints_inter_subset_preimage_Ioo hx,
        fun y hy ↦ hs (mem_image_of_mem f hy) (mem_image_of_mem f hx)⟩

/-- A Weinstein cobordism without critical points in its region is elementary. -/
theorem isElementary_of_criticalPoints_inter_eq_empty (h : IsWeinsteinCobordism ω X f a b)
    (he : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b = ∅) :
    IsElementaryWeinsteinCobordism ω X f a b :=
  h.isElementary_iff.2 (by simp [he])

end IsWeinsteinCobordism

namespace IsElementaryWeinsteinCobordism

/-- Reparametrizing the function of an elementary Weinstein cobordism between `a` and `b` by a
smooth strictly increasing `h` with `h' > 0` at every value of `f` gives an elementary Weinstein
cobordism between `h a` and `h b`, as long as `h ∘ f` is proper and bounded below. -/
theorem comp (hW : IsElementaryWeinsteinCobordism ω X f a b) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hmono : StrictMono h) (hpos : ∀ x, 0 < deriv h (f x))
    (hp : IsProperMap (h ∘ f))
    (hb : BddBelow (range (h ∘ f))) :
    IsElementaryWeinsteinCobordism ω X (h ∘ f) (h a) (h b) := by
  have hc := hW.toIsWeinsteinCobordism.comp hh hmono hpos hp hb
  refine hc.isElementary_iff.2 ?_
  have hf := hW.isWeinsteinStructure.isGeneralizedMorse.contMDiff.mdifferentiable (by simp)
  have hcrit : criticalPoints 𝓘(ℝ, E) (h ∘ f) = criticalPoints 𝓘(ℝ, E) f :=
    ext fun x ↦ mem_criticalPoints_scalar_comp_iff (hf x) (hpos x).ne'
  have hI : h ⁻¹' Icc (h a) (h b) = Icc a b := ext fun _ ↦ by simp [hmono.le_iff_le]
  rw [hcrit, preimage_comp, hI, image_comp]
  exact (hW.toIsWeinsteinCobordism.isElementary_iff.1 hW).image h

/-- A diffeomorphism `Φ : M' → M` pulls an elementary Weinstein cobordism `(ω, X, f)` between `a`
and `b` back to an elementary Weinstein cobordism `(Φ^* ω, Φ^* X, f ∘ Φ)` between the same
levels. -/
theorem pullback (hW : IsElementaryWeinsteinCobordism ω X f a b) {M' : Type*}
    [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M']
    (Φ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M' M (⊤ : ℕ∞)) :
    IsElementaryWeinsteinCobordism (SmoothForm.mpullback Φ Φ.contMDiff ω)
      (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ X) (f ∘ Φ) a b := by
  obtain ⟨c, hc, hsub⟩ := hW.exists_criticalPoints_inter_subset
  refine ⟨hW.toIsWeinsteinCobordism.pullback Φ, c, hc, fun x ⟨hx, hxab⟩ ↦ ?_⟩
  rw [(Φ.isLocalDiffeomorph x).mem_criticalPoints_comp_iff (by simp)] at hx
  exact hsub ⟨hx, hxab⟩

end IsElementaryWeinsteinCobordism

/-! ### The radial example -/

section Radial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The radial Weinstein structure gives elementary cobordisms.** Let `V` be a real inner
product space of finite dimension with a linear symplectic form `ω`, for instance `ℂⁿ`. For
nonzero levels `a < b`, the constant form `ω`, the radial field `x ↦ x / 2` and the function
`x ↦ ‖x‖ ^ 2` form an elementary Weinstein cobordism between `a` and `b`: its only critical point
is the origin, on the level `0`. When `a < 0 < b` the region is the closed ball of radius `√b`
around it; when `0 < a` it is a spherical shell without critical points. -/
theorem isElementaryWeinsteinCobordism_norm_sq (ω : SymplecticForm V) (hab : a < b)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    IsElementaryWeinsteinCobordism ω.constSmooth (fun x : V ↦ (2⁻¹ : ℝ) • x)
      (fun x ↦ ‖x‖ ^ 2) a b := by
  have h : IsWeinsteinCobordism ω.constSmooth (fun x : V ↦ (2⁻¹ : ℝ) • x) (fun x ↦ ‖x‖ ^ 2) a b :=
    ⟨isWeinsteinStructure_constSmooth_norm_sq ω, hab, isRegularValue_norm_sq ha,
      isRegularValue_norm_sq hb⟩
  refine h.isElementary_iff.2 ((subsingleton_singleton (a := ‖(0 : V)‖ ^ 2)).anti ?_)
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  rw [mem_criticalPoints_iff_fderiv_eq_zero, fderiv_norm_sq_eq_zero_iff] at hx
  simp [hx]

end Radial

end SymplecticGeometry

end
