/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.TwistCore
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint
import SymplecticGeometry.Topology.VectorBundle.ZeroSet
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.CodRestrict
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.Restriction
import TauCeti.Geometry.Manifold.Instances.Cylinder
import TauCeti.Topology.VectorBundle.Trivialization
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# The map of the Riemann sphere given by two sections of `𝒪(k)`

Let `s` and `t` be `C^n` sections of the line bundle `𝒪(k) = OnePoint.twistCore k` on the
Riemann sphere, regarded as a real vector bundle over the underlying real surface, with no common
zero. Since `s x` and `t x` lie in the same line, the point `[s x : t x]` of `ℙ¹(ℂ)` is well
defined; read through Mathlib's identification `OnePoint.equivProjectivization` of `OnePoint ℂ`
with `ℙ¹(ℂ)`, it is `s x / t x` where `t x ≠ 0` and `∞` where `t x = 0`.

## Main definitions and results

* `OnePoint.equivProjectivization_symm_mk_eventuallyEq_coe_div`: near a point where `t` does not
  vanish, `x ↦ [s x : t x]` is the inclusion of `ℂ` applied to the quotient `s / t`.
* `OnePoint.equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div`: near a point where `s`
  does not vanish, it is the inverse of the inverted chart `OnePoint.invChart` applied to `t / s`.
* `OnePoint.vec_trivialization_ne_zero_twistCore`: in a trivialization of `𝒪(k)`, the
  coordinates of two vectors of a fibre over its base set do not both vanish unless the vectors
  do.
* `OnePoint.mk_trivialization_twistCore`: in such a trivialization, `[a : b]` is the point given
  by the coordinates of `a` and `b`.
* `OnePoint.contMDiff_equivProjectivization_symm_mk_twistCore`: the map `x ↦ [s x : t x]` is
  `C^n`, for sections written as functions `OnePoint ℂ → ℂ`, as Tau Ceti writes them.
* `OnePoint.ratioMap`: that map, as an element of `C^n⟮𝓘(ℝ, ℂ), OnePoint ℂ; 𝓘(ℝ, ℂ), OnePoint ℂ⟯`,
  for a pair `(s, t)` of `C^n` sections of `𝒪(k)` without common zero.
* `OnePoint.ratioMap_apply`: its value, through `OnePoint.equivProjectivization`.
* `OnePoint.ratioMap_apply_of_ne_zero`: where `t x ≠ 0`, the value is `s x / t x`.
* `OnePoint.ratioMap_apply_of_eq_zero`: where `t x = 0`, the value is `∞`.
* `OnePoint.ratioMap_apply_eq_invChart_symm`: where `s x ≠ 0`, the value is the inverse of the
  inverted chart applied to `t x / s x`.
* `OnePoint.continuous_ratioMap`: `ratioMap` is continuous from the pairs of sections, with the
  frame topology of a covering frame system, to the `C^n` maps of the sphere, with the weak
  Whitney topology.

The fibres of `𝒪(k)` are `ℂ`, but not reducibly so, so the division of two values of sections
does not elaborate; the value lemmas of `ratioMap` therefore take the values as complex numbers
`a` and `b` with `s x = a` and `t x = b`.

Smoothness is read in the coordinates of a trivialization of `𝒪(k)`: over its base set, the
fibre maps are multiplications by nonzero complex numbers, so `[s : t]` is `[a : b]` for the
coordinates `a` and `b` of `s` and `t`, which are `C^n` complex functions without common zero
there; `OnePoint.contMDiff_equivProjectivization_symm_mk` then applies.
`SymplecticGeometry.contMDiff_uniformizingMap` is derived from these results.

For continuity, the weak Whitney topology is local in the source
(`ContMDiffMap.continuous_of_forall_continuous_restrict_manifold`), so it suffices to work over
the base set of one trivialization of `𝒪(k)`. There the fibre maps are multiplications by
nonzero complex numbers, so `[s : t]` is the fixed `C^n` map `(a, b) ↦ [a : b]` on the nonzero
pairs of `ℂ × ℂ`, composed with the pair of coordinates of `s` and `t`. These coordinates depend
continuously on the sections (Tau Ceti's
`ContMDiffSection.continuous_frameCoordinates_of_cover`), and pairing, corestriction to an open
set and composition with a fixed map are continuous for the weak Whitney topologies
(`ContMDiffMap.continuous_prodMk_manifoldWeakWhitney`,
`ContMDiffMap.continuous_codRestrict_manifoldWeakWhitney`,
`ContMDiffMap.continuous_postcomp_manifoldWeakWhitney`).

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak Whitney topology)
-/

public section

open Bundle Filter TauCeti
open scoped Manifold ContDiff Topology OnePoint VectorBundle.ComplexToReal

noncomputable section

namespace OnePoint

variable {k : ℤ} {n : ℕ∞ω} {s t : OnePoint ℂ → ℂ} {x : OnePoint ℂ}

/-- Near a point where the section `t` of `𝒪(k)`, continuous there, does not vanish,
`y ↦ [s y : t y]` is the inclusion of `ℂ` applied to the quotient `s / t`. -/
theorem equivProjectivization_symm_mk_eventuallyEq_coe_div (hst : ∀ y, ![s y, t y] ≠ 0)
    (ht : ContinuousAt (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (t y)) x)
    (hx : t x ≠ 0) :
    (fun y ↦ (equivProjectivization ℂ).symm (Projectivization.mk ℂ ![s y, t y] (hst y))) =ᶠ[𝓝 x]
      (↑) ∘ fun y ↦ s y / t y := by
  filter_upwards [VectorBundle.eventually_ne_zero ℂ (b := id) ht hx] with y hy
  exact equivProjectivization_symm_mk_of_ne_zero (hst y) hy

/-- Near a point where the section `s` of `𝒪(k)`, continuous there, does not vanish,
`y ↦ [s y : t y]` is the inverse of the inverted chart applied to the quotient `t / s`. -/
theorem equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div
    (hst : ∀ y, ![s y, t y] ≠ 0)
    (hs : ContinuousAt (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (s y)) x)
    (hx : s x ≠ 0) :
    (fun y ↦ (equivProjectivization ℂ).symm (Projectivization.mk ℂ ![s y, t y] (hst y))) =ᶠ[𝓝 x]
      invChart.symm ∘ fun y ↦ t y / s y := by
  filter_upwards [VectorBundle.eventually_ne_zero ℂ (b := id) hs hx] with y hy
  exact equivProjectivization_symm_mk_eq_invChart_symm (hst y) hy

/-- In a trivialization of `𝒪(k)`, over a point of its base set, the coordinates of two vectors
of the fibre that do not both vanish do not both vanish. -/
theorem vec_trivialization_ne_zero_twistCore
    (e : Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) k).Fiber)) [e.IsLinear ℂ]
    {y : OnePoint ℂ} (hy : y ∈ e.baseSet) {a b : (twistCore (𝕜 := ℂ) k).Fiber y}
    (h : (![a, b] : Fin 2 → ℂ) ≠ 0) : (![(e ⟨y, a⟩).2, (e ⟨y, b⟩).2] : Fin 2 → ℂ) ≠ 0 :=
  fun h' ↦ h <| by
    have h₀ := congrFun h' 0
    have h₁ := congrFun h' 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h₀ h₁
    ext i
    fin_cases i
    -- The entries are `a` and `b`, read in `ℂ`, which the fibres are by definition.
    exacts [(e.snd_apply_eq_zero_iff ℂ (v := ⟨y, a⟩) hy).mp h₀,
      (e.snd_apply_eq_zero_iff ℂ (v := ⟨y, b⟩) hy).mp h₁]

/-- In a trivialization of `𝒪(k)`, over a point of its base set, the point `[a : b]` of `ℙ¹(ℂ)`
does not change when `a` and `b` are replaced by their coordinates. -/
theorem mk_trivialization_twistCore (e : Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) k).Fiber))
    [e.IsLinear ℂ] {y : OnePoint ℂ} (hy : y ∈ e.baseSet)
    {a b : (twistCore (𝕜 := ℂ) k).Fiber y} (h : (![a, b] : Fin 2 → ℂ) ≠ 0)
    (h' : (![(e ⟨y, a⟩).2, (e ⟨y, b⟩).2] : Fin 2 → ℂ) ≠ 0) :
    Projectivization.mk ℂ _ h' = Projectivization.mk ℂ _ h := by
  -- The fibre map of `e` at `y`, read as a `ℂ`-linear map of `ℂ`, which each fibre is.
  let L : ℂ →L[ℂ] ℂ :=
    (e.continuousLinearEquivAt ℂ y hy : (twistCore (𝕜 := ℂ) k).Fiber y →L[ℂ] ℂ)
  have hL (v : ℂ) : L 1 * v = L v := by
    rw [mul_comm, ← smul_eq_mul, ← L.map_smul, smul_eq_mul, mul_one]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ h' h).mpr ⟨L 1, ?_⟩
  ext i
  fin_cases i
  -- The entries are `L a` and `L b`: a fibre of `𝒪(k)` is `ℂ` by definition.
  exacts [hL a, hL b]

/-- **The map `[s : t]` is smooth.** For `C^n` sections `s` and `t` of `𝒪(k)`, for the real
structure, without common zero, the map `x ↦ [s x : t x]` of the Riemann sphere, read through
`OnePoint.equivProjectivization`, is `C^n`. -/
theorem contMDiff_equivProjectivization_symm_mk_twistCore
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (s y)))
    (ht : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (t y)))
    (hst : ∀ y, ![s y, t y] ≠ 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (fun y ↦ (equivProjectivization ℂ).symm (Projectivization.mk ℂ ![s y, t y] (hst y))) := by
  intro x
  -- Work on the base set `U` of the trivialization `e` at `x`, in the coordinates of `e`.
  let e := trivializationAt ℂ (twistCore (𝕜 := ℂ) k).Fiber x
  let U : TopologicalSpace.Opens (OnePoint ℂ) := e.baseSetOpens
  have hU : (U : Set (OnePoint ℂ)) ⊆ e.baseSet := e.coe_baseSetOpens.subset
  let c (u : Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯) :=
    e.frameCoordinates (I := 𝓘(ℝ, ℂ)) (n := n) (U := U) hU u
  have hc (u : Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯) (y : U) :
      c u y = (e ⟨y, u y⟩).2 :=
    Bundle.Trivialization.frameCoordinates_apply _ _ _ _
  have hne₀ (y : U) : (![(e ⟨y, s y⟩).2, (e ⟨y, t y⟩).2] : Fin 2 → ℂ) ≠ 0 :=
    vec_trivialization_ne_zero_twistCore e (hU y.property) (hst y)
  have hne (y : U) : (![c ⟨s, hs⟩ y, c ⟨t, ht⟩ y] : Fin 2 → ℂ) ≠ 0 := by
    rw [hc, hc]
    exact hne₀ y
  have hx : x ∈ U :=
    Bundle.Trivialization.mem_baseSetOpens_iff.2 (mem_baseSet_trivializationAt ℂ _ x)
  refine (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).1 ?_
  refine (contMDiff_equivProjectivization_symm_mk (c ⟨s, hs⟩).contMDiff (c ⟨t, ht⟩).contMDiff
    hne _).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  have h := mk_trivialization_twistCore e (hU y.property) (hst y) (hne₀ y)
  simp only [hc] at h ⊢
  exact congrArg _ h.symm

variable (p : {p : Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ ×
  Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ // ∀ x, (![p.1 x, p.2 x] : Fin 2 → ℂ) ≠ 0})

/-- The map `x ↦ [s x : t x]` of the Riemann sphere, for a pair `(s, t)` of `C^n` sections of
`𝒪(k)`, for the real structure, without common zero, as a `C^n` map. Its value is read through
the identification `OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℙ¹(ℂ)`. -/
def ratioMap : C^n⟮𝓘(ℝ, ℂ), OnePoint ℂ; 𝓘(ℝ, ℂ), OnePoint ℂ⟯ :=
  ⟨fun x ↦ (equivProjectivization ℂ).symm
      (Projectivization.mk ℂ (![p.val.1 x, p.val.2 x] : Fin 2 → ℂ) (p.property x)),
    contMDiff_equivProjectivization_symm_mk_twistCore p.val.1.contMDiff p.val.2.contMDiff
      p.property⟩

/-- The value of `ratioMap` at `x` is the point `[s x : t x]` of `ℙ¹(ℂ)`, read in
`OnePoint ℂ`. -/
@[simp]
theorem ratioMap_apply (x : OnePoint ℂ) :
    ratioMap p x = (equivProjectivization ℂ).symm
      (Projectivization.mk ℂ (![p.val.1 x, p.val.2 x] : Fin 2 → ℂ) (p.property x)) :=
  (rfl)

/-- At a point where `t` takes the nonzero value `b` and `s` the value `a`, `ratioMap` takes the
value `a / b`. The values are taken as complex numbers, which the fibres of `𝒪(k)` are. -/
theorem ratioMap_apply_of_ne_zero {a b : ℂ} (ha : p.val.1 x = a) (hb : p.val.2 x = b)
    (hb₀ : b ≠ 0) : ratioMap p x = ((a / b : ℂ) : OnePoint ℂ) := by
  subst ha hb
  rw [ratioMap_apply]
  exact equivProjectivization_symm_mk_of_ne_zero (p.property x) hb₀

/-- At a zero of `t`, `ratioMap` takes the value `∞`. -/
theorem ratioMap_apply_of_eq_zero (hx : p.val.2 x = 0) : ratioMap p x = (∞ : OnePoint ℂ) := by
  rw [ratioMap_apply, equivProjectivization_symm_apply_mk]
  split_ifs with h
  · rfl
  · exact absurd hx h

/-- At a point where `s` takes the nonzero value `a` and `t` the value `b`, `ratioMap` takes the
value of the inverse of the inverted chart at `b / a`. -/
theorem ratioMap_apply_eq_invChart_symm {a b : ℂ} (ha : p.val.1 x = a) (hb : p.val.2 x = b)
    (ha₀ : a ≠ 0) : ratioMap p x = invChart.symm (b / a) := by
  subst ha hb
  rw [ratioMap_apply]
  exact equivProjectivization_symm_mk_eq_invChart_symm (p.property x) ha₀

section Continuity

open TopologicalSpace
open scoped TauCeti.ManifoldWeakWhitney TauCeti.ComplexManifold

/-- The entries of a nonzero pair of complex numbers form a nonzero vector of `ℂ²`. -/
private theorem vec_ne_zero_of_mem_puncturedSpace (q : puncturedSpace (ℂ × ℂ)) :
    (![(q : ℂ × ℂ).1, (q : ℂ × ℂ).2] : Fin 2 → ℂ) ≠ 0 := by
  simpa [Matrix.cons_eq_zero_iff, Prod.ext_iff] using mem_puncturedSpace.1 q.property

/-- The map `(a, b) ↦ [a : b]` from the nonzero pairs to the Riemann sphere, as a `C^n` map. -/
private def projMk : C^n⟮𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ), puncturedSpace (ℂ × ℂ); 𝓘(ℝ, ℂ), OnePoint ℂ⟯ :=
  ⟨fun q ↦ (equivProjectivization ℂ).symm
      (Projectivization.mk ℂ _ (vec_ne_zero_of_mem_puncturedSpace q)),
    contMDiff_equivProjectivization_symm_mk (contMDiff_fst.comp contMDiff_subtypeVal)
      (contMDiff_snd.comp contMDiff_subtypeVal) vec_ne_zero_of_mem_puncturedSpace⟩

private theorem projMk_apply (q : puncturedSpace (ℂ × ℂ)) :
    projMk (n := n) q = (equivProjectivization ℂ).symm
      (Projectivization.mk ℂ _ (vec_ne_zero_of_mem_puncturedSpace q)) :=
  (rfl)

/-- **The map `[s : t]` depends continuously on `(s, t)`.** Give the `C^n` sections of `𝒪(k)`
the topology `ContMDiffSection.frameTopology e U hU` of a frame system whose domains cover the
sphere, and the pairs of sections without common zero the subspace topology of the product.
Then `OnePoint.ratioMap` is continuous for the weak Whitney topology on `C^n` maps of the
sphere. -/
theorem continuous_ratioMap {ι : Type*}
    (e : ι → Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) k).Fiber))
    [∀ i, MemTrivializationAtlas (e i)] (U : ι → Opens (OnePoint ℂ))
    (hU : ∀ i, (U i : Set (OnePoint ℂ)) ⊆ (e i).baseSet) (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := n) e U hU
    Continuous (ratioMap (k := k) (n := n)) := by
  intro _
  -- Check continuity on the base set of the trivialization at each point.
  let e' := trivializationAt ℂ (twistCore (𝕜 := ℂ) k).Fiber
  let U' (x : OnePoint ℂ) := (e' x).baseSetOpens
  have hU' : ∀ x, (U' x : Set (OnePoint ℂ)) ⊆ (e' x).baseSet := fun x ↦
    (e' x).coe_baseSetOpens.subset
  refine ContMDiffMap.continuous_of_forall_continuous_restrict_manifold U'
    (FiberBundle.exists_mem_baseSetOpens_trivializationAt ℂ _) fun x ↦ ?_
  -- There, `[s : t]` is `projMk` composed with the pair of coordinates of `s` and `t`.
  let c (s : Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯) :=
    (e' x).frameCoordinates (I := 𝓘(ℝ, ℂ)) (n := n) (U := U' x) (hU' x) s
  have hc : Continuous c := ContMDiffSection.continuous_frameCoordinates_of_cover e U hU hcover
    (e' x) (U' x) (hU' x)
  have hpair : Continuous fun p : {p : Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ ×
      Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ // ∀ x, (![p.1 x, p.2 x] : Fin 2 → ℂ) ≠ 0} ↦
      (c p.val.1).prodMk (c p.val.2) :=
    ContMDiffMap.continuous_prodMk_manifoldWeakWhitney.comp
      ((hc.comp (continuous_fst.comp continuous_subtypeVal)).prodMk
        (hc.comp (continuous_snd.comp continuous_subtypeVal)))
  have hmem (p : {p : Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ ×
      Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ // ∀ x, (![p.1 x, p.2 x] : Fin 2 → ℂ) ≠ 0})
      (y : U' x) : (c p.val.1).prodMk (c p.val.2) y ∈ puncturedSpace (ℂ × ℂ) := by
    refine mem_puncturedSpace.2 fun h ↦ ?_
    obtain ⟨h₁, h₂⟩ := Prod.mk_eq_zero.mp h
    simp only [c, Bundle.Trivialization.frameCoordinates_apply] at h₁ h₂
    refine vec_trivialization_ne_zero_twistCore (e' x) (hU' x y.property) (p.property y) ?_
    ext i
    fin_cases i <;> simp [h₁, h₂]
  convert (ContMDiffMap.continuous_postcomp_manifoldWeakWhitney projMk).comp
    (hpair.codRestrict_manifoldWeakWhitney (puncturedSpace (ℂ × ℂ)) hmem) using 1
  funext p
  ext y
  simp only [Function.comp_apply, ContMDiffMap.restrict_apply, ContMDiffMap.comp_apply,
    ratioMap_apply, projMk_apply, ContMDiffMap.coe_codRestrict_apply, ContMDiffMap.prodMk_apply,
    c,
    Bundle.Trivialization.frameCoordinates_apply]
  congr 1
  exact (mk_trivialization_twistCore (e' x) (hU' x y.property) _ _).symm

end Continuity

end OnePoint

end
