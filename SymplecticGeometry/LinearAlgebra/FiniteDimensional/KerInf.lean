/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The kernel of a surjection cut by two linear forms

Let `ℓ : V → W` be a surjective linear map between finite-dimensional vector spaces with
`dim V = dim W + 2`, so that its kernel is a plane, and let `f` and `g` be linear forms on `V`.
Suppose the plane contains a vector `v` with `f v ≠ 0` and `g v = 0`. Then the line
`ker ℓ ∩ ker f` meets `ker g` only in `0` exactly when `g` does not vanish on the plane
(`LinearMap.ker_inf_ker_inf_ker_eq_bot_iff`).

This is the linear algebra behind the transversality of a pencil of hyperplanes to a projective
hypersurface: there `ℓ` is a tuple of linear forms, `v` a point of their common zero line, `f` a
coordinate with `f v ≠ 0` and `g` the differential of the polynomial at `v`, which vanishes at `v`
by Euler's identity.
-/

public section

open Module

namespace LinearMap

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/-- Let `ℓ : V → W` be surjective with `dim V = dim W + 2`, and let `f` and `g` be linear forms
on `V`, with a vector `v` in the kernel of `ℓ` such that `f v ≠ 0` and `g v = 0`. Then the common
kernel of `ℓ`, `f` and `g` is zero exactly when `g` does not vanish on the kernel of `ℓ`. -/
theorem ker_inf_ker_inf_ker_eq_bot_iff {ℓ : V →ₗ[K] W} (hℓ : Function.Surjective ℓ)
    (hdim : finrank K V = finrank K W + 2) {f g : V →ₗ[K] K} {v : V} (hℓv : ℓ v = 0)
    (hfv : f v ≠ 0) (hgv : g v = 0) :
    ker ℓ ⊓ ker f ⊓ ker g = ⊥ ↔ ∃ w, ℓ w = 0 ∧ g w ≠ 0 := by
  -- The common kernel of `ℓ` and `f` is a line: the kernel of `f` is a hyperplane that does not
  -- contain the plane `ker ℓ`.
  have hℓk : finrank K (ker ℓ) = 2 := by
    have := ℓ.finrank_range_add_finrank_ker
    rw [range_eq_top.2 hℓ, finrank_top] at this
    omega
  have hfk : finrank K (ker f) + 1 = finrank K V := by
    have := f.finrank_range_add_finrank_ker
    rw [range_eq_top.2 fun c ↦ ⟨(c / f v) • v, by simp [div_mul_cancel₀ _ hfv]⟩,
      finrank_top, finrank_self] at this
    omega
  have hsup : finrank K (ker f) < finrank K ↥(ker ℓ ⊔ ker f) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_right fun h ↦
      hfv (h ▸ Submodule.mem_sup_left (mem_ker.2 hℓv) :))
  have hT : finrank K ↥(ker ℓ ⊓ ker f) = 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (ker ℓ) (ker f)
    have h2 := Submodule.finrank_le (ker ℓ ⊔ ker f)
    omega
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.1 hT.ge)
    refine ⟨x, hx.1, fun hgx ↦ hx0 ?_⟩
    have : x ∈ ker ℓ ⊓ ker f ⊓ ker g := ⟨hx, hgx⟩
    rwa [h, Submodule.mem_bot] at this
  · rintro ⟨w, hℓw, hgw⟩
    refine eq_bot_iff.2 fun x hx ↦ ?_
    obtain ⟨⟨hxℓ, hxf⟩, hxg⟩ := hx
    by_contra hx0
    -- Projecting `w` along `v` into the line `ker ℓ ∩ ker f` keeps `g w`, so `x`, which spans
    -- that line, cannot lie in `ker g`.
    have hw₁ : w - (f w / f v) • v ∈ ker ℓ ⊓ ker f :=
      ⟨by simp [hℓw, hℓv], by simp [div_mul_cancel₀ _ hfv]⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨x, hxℓ, hxf⟩ : ↥(ker ℓ ⊓ ker f))
      (fun h ↦ hx0 (congrArg Subtype.val h))).1 hT ⟨_, hw₁⟩
    have := congrArg (fun y : ↥(ker ℓ ⊓ ker f) ↦ g y) hc
    simp only [SetLike.val_smul, map_smul, map_sub, hgv, smul_zero, sub_zero] at this
    exact hgw (by rw [← this, mem_ker.1 hxg, smul_zero])

end LinearMap
