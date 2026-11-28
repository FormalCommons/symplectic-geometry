/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import TauCeti.Geometry.Symplectic.Manifold.Moser.Path
import SymplecticGeometry.Geometry.Symplectic.Manifold.Surface
import SymplecticGeometry.Geometry.Manifold.DeRham.Integration.Bijective
import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Compact
import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
import SymplecticGeometry.Geometry.Symplectic.Moser.Parameter

/-!
# Moser's theorem for area forms on closed surfaces

Let `M` be a closed connected surface with an orientation `o`, and let `ω₀` and `σ` be smooth
two-forms on `M` that are positive for `o`: both take positive values on every positively oriented
tangent basis. If `∫_M σ = ∫_M ω₀`, then there is a diffeotopy `Ψ` of `M`, which starts at the
identity, with `Ψ_1^* σ = ω₀`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_integralTopForm_eq`). In particular
its time-one map `ψ = Ψ_1` is a diffeomorphism of `M` with `ψ^* σ = ω₀`
(`TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_eq_of_integralTopForm_eq`).

The same holds with a parameter: a two-form `σ` on `P × M` whose slices `σ_p` are positive for
`o` with the integral of `ω₀` gives a diffeomorphism `(p, x) ↦ (p, χ_p x)` of `P × M` with
`χ_p^* σ_p = ω₀`, and each `χ_p` preserves `o`
(`TauCeti.SmoothTwoForm.exists_diffeomorph_prod_mpullback_eq_of_integralTopForm_eq`). Here the
differences `σ_p - ω₀` are exact, they have a smooth family of primitives since `M` has a finite
good cover (`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq`), and Moser's argument with
a parameter (`TauCeti.SmoothTwoForm.exists_diffeomorph_prod_mpullback_eq_of_mextDeriv_eq_sub`)
gives `χ`.

The proof is Moser's argument along the segment `σ_t = ω₀ + t (σ - ω₀)`, `t ∈ [0, 1]`.

1. Every `σ_t` is positive for `o`, as positivity is kept along segments, so it is symplectic
   (`TauCeti.SmoothTwoForm.isSymplectic_add_smul_sub`): on a surface a nowhere-vanishing
   two-form is symplectic.
2. Since `σ` and `ω₀` have the same integral, `σ - ω₀` is exact on the connected closed surface
   (`TauCeti.sub_mem_exactForms_iff_integralTopForm_eq`); hence so is
   `σ_t - σ_0 = t (σ - ω₀)`.
3. For a primitive `β` of `σ - ω₀`, Tau Ceti's Moser theorem along an exact path
   (`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_add_smoothTransition_smul_eq`) gives an
   isotopy `ψ_t` with `ψ_t^* σ_{c(t)} = ω₀`, `c = Real.smoothTransition`. Its restriction to
   `[0, 1]` (`TauCeti.Diffeotopy.ofReal`) is a diffeotopy `Ψ` whose time-one map is `ψ_1`, and
   `c(1) = 1`.

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_integralTopForm_eq`: two area forms of
  equal integral, positive for the same orientation of a closed connected surface, are related by
  the time-one map of a diffeotopy.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_eq_of_integralTopForm_eq`: the same, with
  only the diffeomorphism.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_prod_mpullback_eq_of_integralTopForm_eq`: the same
  for a family of area forms over a parameter manifold, with orientation-preserving
  diffeomorphisms.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2,
  and §6.2 (the proof of Theorem 6.2.2) for the parametric form.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

open SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

/-- **Moser's theorem for area forms.** Let `M` be a closed surface, connected or empty, with an
orientation `o`, and let `ω₀` and `σ` be smooth two-forms on `M`, both positive on every
positively oriented tangent basis. If `σ` and `ω₀` have the same integral over `M`, then there is a
diffeotopy `Ψ` of `M`, which starts at the identity, whose time-one map `Ψ.final` pulls `σ` back
to `ω₀`. -/
theorem exists_diffeotopy_mpullback_eq_of_integralTopForm_eq [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin 2)) {ω₀ σ : SmoothTwoForm I M}
    (hω : o.IsPositive ω₀.val) (hσ : o.IsPositive σ.val)
    (hint : integralTopForm o σ.val = integralTopForm o ω₀.val) :
    ∃ Ψ : Diffeotopy I ∞ M, SmoothForm.mpullback Ψ.final Ψ.final.contMDiff σ = ω₀ := by
  -- Step 1 gives that every form of the segment is symplectic, and step 2 a primitive `β` of
  -- `σ - ω₀`.
  obtain ⟨β, hβ⟩ : σ - ω₀ ∈ LinearMap.range (mextDerivₗ I 1) :=
    exactForms_succ (I := I) (M := M) 1 ▸ (sub_mem_exactForms_iff_integralTopForm_eq o).2 hint
  -- Step 3: Moser's theorem along the exact path from `ω₀` to `σ`.
  obtain ⟨ψ, hψ, hψ₀, hψσ⟩ := exists_isotopy_mpullback_add_smoothTransition_smul_eq ω₀ σ β
    (by rw [← hβ, mextDerivₗ_apply]) fun _ hs ↦ isSymplectic_add_smul_sub hω hσ hs
  refine ⟨Diffeotopy.ofReal ψ hψ hψ₀, ?_⟩
  rw [Diffeotopy.final_ofReal]
  simpa [Real.smoothTransition.one] using hψσ 1

/-- **Moser's theorem for area forms**, as a diffeomorphism. Let `M` be a closed surface, connected
or empty, with an orientation `o`, and let `ω₀` and `σ` be smooth two-forms on `M`, both positive
on every positively oriented tangent basis. If `σ` and `ω₀` have the same integral over `M`, then
there is a diffeomorphism `ψ` of `M` with `ψ^* σ = ω₀`. -/
theorem exists_diffeomorph_mpullback_eq_of_integralTopForm_eq [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin 2)) {ω₀ σ : SmoothTwoForm I M}
    (hω : o.IsPositive ω₀.val) (hσ : o.IsPositive σ.val)
    (hint : integralTopForm o σ.val = integralTopForm o ω₀.val) :
    ∃ ψ : M ≃ₘ⟮I, I⟯ M, SmoothForm.mpullback ψ ψ.contMDiff σ = ω₀ :=
  let ⟨Ψ, hΨ⟩ := exists_diffeotopy_mpullback_eq_of_integralTopForm_eq o hω hσ hint
  ⟨Ψ.final, hΨ⟩

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [CompleteSpace EP]
  [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] [T2Space P] [BoundarylessManifold IP P]

/-- **Moser's theorem for families of area forms.** Let `M` be a closed surface, connected or
empty, with an orientation `o`, let `P` be a Hausdorff boundaryless manifold modelled on a complete
space, `ω₀` a two-form on `M` positive for `o`, and `σ` a two-form on `P × M` whose slices `σ_p`
are positive for `o` and have the integral of `ω₀`. Then there is a diffeomorphism `Φ` of `P × M`
of the form `(p, x) ↦ (p, χ_p x)`, for diffeomorphisms `χ_p` of `M` preserving `o`, with
`χ_p^* σ_p = ω₀` for every `p`. -/
theorem exists_diffeomorph_prod_mpullback_eq_of_integralTopForm_eq [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin 2)) {ω₀ : SmoothTwoForm I M} (hω : o.IsPositive ω₀.val)
    (σ : SmoothForm (IP.prod I) (P × M) ℝ 2)
    (hσ : ∀ p, o.IsPositive
      (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) σ).val)
    (hint : ∀ p, integralTopForm o
      (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) σ).val =
        integralTopForm o ω₀.val) :
    ∃ Φ : (P × M) ≃ₘ⟮IP.prod I, IP.prod I⟯ (P × M), ∃ χ : P → M ≃ₘ⟮I, I⟯ M,
      (∀ q, Φ q = (q.1, χ q.1 q.2)) ∧
      (∀ p, SmoothForm.mpullback (χ p) (χ p).contMDiff
          (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) σ) = ω₀) ∧
      ∀ p, χ p ∈ Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o := by
  have hE : Module.finrank ℝ E = 2 := by simpa using o.card_eq.symm
  -- The differences `σ_p - ω₀` are exact, with a smooth family of primitives `α p`.
  obtain ⟨α, hα, hdα⟩ := exists_isSmoothFamily_mextDerivₗ_eq (k := 1)
    hasFiniteGoodCover_of_compactSpace
    ((isSmoothFamily_mpullback_prodMk σ).sub (isSmoothFamily_const ω₀))
    fun p ↦ (sub_mem_exactForms_iff_integralTopForm_eq o).2 (hint p)
  obtain ⟨β, hβ⟩ := isSmoothFamily_def.mp hα
  -- Moser's argument with parameters in `P`, along the segments from `ω₀` to `σ_p`.
  obtain ⟨Φ, χ, hΦ, hχ, -⟩ :=
    exists_diffeomorph_prod_mpullback_eq_of_mextDeriv_eq_sub
      (SmoothForm.isClosed_of_finrank_le hE.le ω₀) σ β
      (fun p ↦ by rw [hβ, ← hdα p, mextDerivₗ_apply])
      fun p x s hs ↦ nondegenerate_bilinFormAt_add_smul_sub (hω.isPositiveAt x)
        ((hσ p).isPositiveAt x) hs
  -- Each `χ p` pulls the positive form `σ_p` back to the positive form `ω₀`, so it preserves `o`.
  refine ⟨Φ, χ, hΦ, hχ, fun p ↦
    (Diffeomorph.mem_orientationPreservingSubgroup_iff_isPositive_mpullback (hσ p)).2 ?_⟩
  rw [← SmoothForm.coe_mpullback _ (χ p).contMDiff, hχ p]
  exact hω

end TauCeti.SmoothTwoForm

end
