/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Cayley.Path
public import TauCeti.Topology.Homotopy.HomotopyEquiv
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Contractible

/-!
# Contractible spaces of tame and compatible almost complex structures on a manifold

Let `M` be a Hausdorff σ-compact smooth manifold modelled on a finite-dimensional space. This file
proves, for the `C^∞` topologies on compact sets given by frames of the endomorphism bundle and of
the bundle of alternating two-forms of `TM`:

* for a nondegenerate smooth two-form `σ`, the smooth almost complex structures tamed by `σ`, and
  those compatible with `σ`, form contractible spaces, for Tau Ceti's
  `TauCeti.SmoothAlmostComplexStructure.frameTopology`;
* for a smooth almost complex structure `J`, the smooth two-forms that tame `J`, and those
  compatible with `J`, form contractible spaces;
* for a Riemannian metric `g` on `M`, the map `ω ↦ J_{g,ω}` from the nondegenerate two-forms to
  the smooth almost complex structures is a homotopy equivalence, with homotopy inverse
  `J ↦ ω_{g,J}`;
* `M` has a smooth almost complex structure exactly when it has a nondegenerate smooth two-form,
  and `ω ↦ J_{g,ω}` induces a bijection between the path components of the two spaces;
* for a `σ`-compatible structure `J₀`, Tau Ceti's Cayley path
  `TauCeti.SmoothTwoForm.Compatible.cayleyPath` from `J₀` to a `σ`-tame structure `J` is jointly
  continuous in the time and in `J`, so that, run backwards, it contracts the `σ`-tame structures
  onto `J₀`, relative to `J₀`. This part needs neither the Hausdorff nor the σ-compact
  hypothesis.

Tau Ceti puts no topology on `TauCeti.SmoothTwoForm`, so the spaces of forms are subtypes of
this library's `SymplecticGeometry.Bundle.ContMDiffTwoForm I ⊤ EB (TangentSpace I)`, which
`SymplecticGeometry.Bundle.ContMDiffTwoForm.tangentEquiv` identifies with Tau Ceti's smooth
two-forms, with the frame topology of sections; tameness and compatibility are Tau Ceti's, read
through `tangentEquiv`.

Every statement but the contraction and the contractibility of the tame structures is the case
`V = TM` of a statement for vector bundles in
`SymplecticGeometry/Geometry/Manifold/VectorBundle/Symplectic/ComplexStructure/Contractible.lean`,
carried over by the homeomorphism
`SymplecticGeometry.Bundle.ContMDiffComplexStructure.tangentHomeomorph` and the comparisons
`SymplecticGeometry.Bundle.ContMDiffTwoForm.tames_tangentEquiv_iff` and
`SymplecticGeometry.Bundle.ContMDiffTwoForm.compatible_tangentEquiv_iff`; for the continuity of
Tau Ceti's Cayley path it is
`SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.continuous_cayleyPath`. The contraction is
built as `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.cayleyContraction` is, with Tau
Ceti's path and the fixed point `J₀` (`TauCeti.SmoothTwoForm.Compatible.cayleyPath_self`), and
the tame structures are contractible through it, for a compatible `J₀` that
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible` gives.
It is the counterpart, for smooth structures on `M`, of Tau Ceti's linear
`TauCeti.SymplecticForm.Compatible.cayleyContraction`, whose name it takes.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleSpace_tames`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleSpace_compatible`: the almost complex
  structures tamed by, or compatible with, a nondegenerate form form contractible spaces.
* `TauCeti.SmoothAlmostComplexStructure.contractibleSpace_tames`,
  `TauCeti.SmoothAlmostComplexStructure.contractibleSpace_compatible`: the two-forms that tame, or
  are compatible with, an almost complex structure form contractible spaces.
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.exists_homotopyEquiv_smoothAlmostComplexStructure`:
  for a metric `g`, the map `ω ↦ J_{g,ω}` is a homotopy equivalence.
* `TauCeti.SmoothAlmostComplexStructure.nonempty_iff_exists_isNondegenerate`: almost complex
  structures exist exactly when nondegenerate two-forms do.
* `Bundle.ContMDiffTwoForm.exists_zerothHomotopyEquiv_smoothAlmostComplexStructure`:
  the bijection of path components induced by `ω ↦ J_{g,ω}`, by Tau Ceti's
  `ContinuousMap.HomotopyEquiv.zerothHomotopyCongr`.
* `SymplecticGeometry.contractibleSpace_compatible_tames_tangent`: the conjunction of these
  statements.
* `TauCeti.SmoothTwoForm.Compatible.continuous_cayleyPath`: the joint continuity of Tau Ceti's
  Cayley path from a compatible structure.
* `TauCeti.SmoothTwoForm.Compatible.cayleyContraction`, with
  `TauCeti.SmoothTwoForm.Compatible.cayleyContraction_apply`: the contraction of the `σ`-tame
  structures onto a `σ`-compatible `J₀`, as a homotopy relative to `{J₀}`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.6.4 and Proposition 4.1.1
-/

public section

noncomputable section

open _root_.Bundle Set TopologicalSpace
open scoped Manifold ContinuousMap

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {ι κ : Type*}
  (e : ι → Trivialization (EB →L[ℝ] EB)
    (π (EB →L[ℝ] EB) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (e' : κ → Trivialization (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (π (EB [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (e' j)]
  (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)

open SymplecticGeometry.Bundle

/-! ### The Cayley contraction onto a compatible structure -/

namespace TauCeti.SmoothTwoForm.Compatible

variable {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}

omit [T2Space M] [SigmaCompactSpace M] in
/-- For a covering frame system of the endomorphism bundle of `TM`, the Cayley path from a
`σ`-compatible structure `J₀` to a `σ`-tame structure `J` is jointly continuous in the time and in
`J`, for the `C^∞` topology `TauCeti.SmoothAlmostComplexStructure.frameTopology`. -/
theorem continuous_cayleyPath (h₀ : σ.Compatible J₀) (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    Continuous fun p : ℝ × {J : SmoothAlmostComplexStructure I M // σ.Tames J} ↦
      h₀.cayleyPath p.2.property p.1 := by
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := ⊤) e U hU
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  let H := ContMDiffComplexStructure.tangentHomeomorph e U hU
  have h₀' : (ContMDiffTwoForm.tangentEquiv.symm σ).Compatible (H.symm J₀) := by
    rw [← ContMDiffTwoForm.compatible_tangentEquiv_iff]
    simpa [H] using h₀
  have hT (J : {J : SmoothAlmostComplexStructure I M // σ.Tames J}) :
      (ContMDiffTwoForm.tangentEquiv.symm σ).Tames (H.symm J.val) := by
    rw [← ContMDiffTwoForm.tames_tangentEquiv_iff]
    simpa [H] using J.property
  refine (H.continuous.comp ((h₀'.continuous_cayleyPath e U hU hcover).comp
    (continuous_fst.prodMk ((H.symm.continuous.comp (continuous_subtypeVal.comp
      continuous_snd)).subtype_mk fun p ↦ hT p.2)))).congr fun p ↦ ?_
  ext x v
  simp [H, cayleyPath_toEndomorphism]

omit [T2Space M] [SigmaCompactSpace M] in
/-- For a covering frame system of the endomorphism bundle of `TM`, the Cayley paths run backwards
contract the space of `σ`-tame smooth almost complex structures onto a `σ`-compatible structure
`J₀`, relative to `J₀`: at time `t` the homotopy sends `J` to the Cayley path from `J₀` to `J` at
time `1 - t`, so it starts at the identity, ends at the constant map at `J₀`, and fixes `J₀` at
every time. -/
noncomputable def cayleyContraction (h₀ : σ.Compatible J₀) (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    (ContinuousMap.id {J : SmoothAlmostComplexStructure I M // σ.Tames J}).HomotopyRel
      (ContinuousMap.const _ ⟨J₀, h₀.tames⟩) {⟨J₀, h₀.tames⟩} :=
  letI := SmoothAlmostComplexStructure.frameTopology e U hU
  { toFun := fun p ↦ ⟨h₀.cayleyPath p.2.property (1 - p.1), h₀.tames_cayleyPath p.2.property _⟩
    continuous_toFun := ((h₀.continuous_cayleyPath e U hU hcover).comp
      ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).prodMk
        continuous_snd)).subtype_mk _
    map_zero_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_one_le J.property (by simp))
    map_one_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_nonpos J.property (by simp))
    prop' := fun t J hJ ↦ by
      obtain rfl := hJ
      exact Subtype.ext (h₀.cayleyPath_self _) }

omit [T2Space M] [SigmaCompactSpace M] in
/-- At time `t`, the Cayley contraction onto `J₀` sends a `σ`-tame structure `J` to the Cayley
path from `J₀` to `J` at time `1 - t`. -/
@[simp]
theorem cayleyContraction_apply (h₀ : σ.Compatible J₀) (hcover : ∀ x, ∃ i, x ∈ U i)
    (t : unitInterval) (J : {J : SmoothAlmostComplexStructure I M // σ.Tames J}) :
    (h₀.cayleyContraction e U hU hcover (t, J) : SmoothAlmostComplexStructure I M) =
      h₀.cayleyPath J.property (1 - t) :=
  (rfl)

end TauCeti.SmoothTwoForm.Compatible

/-! ### Structures tamed by, or compatible with, a nondegenerate form -/

namespace TauCeti.SmoothTwoForm

variable {σ : SmoothTwoForm I M}

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, the smooth almost
complex structures tamed by a nondegenerate smooth two-form `σ` form a contractible space, for the
`C^∞` topology in any covering frames of the endomorphism bundle of `TM`. It is contracted to a
`σ`-compatible structure `J₀` along Tau Ceti's Cayley paths from `J₀`. -/
theorem IsNondegenerate.contractibleSpace_tames (hσ : σ.IsNondegenerate)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    ContractibleSpace {J : SmoothAlmostComplexStructure I M // σ.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  obtain ⟨J₀, h₀⟩ := hσ.exists_compatible
  exact (contractible_iff_id_nullhomotopic _).2
    ⟨⟨J₀, h₀.tames⟩, ⟨(h₀.cayleyContraction e U hU hcover).toHomotopy⟩⟩

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, the smooth almost
complex structures compatible with a nondegenerate smooth two-form `σ` form a contractible space,
for the `C^∞` topology in any covering frames of the endomorphism bundle of `TM`. -/
theorem IsNondegenerate.contractibleSpace_compatible (hσ : σ.IsNondegenerate)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    ContractibleSpace {J : SmoothAlmostComplexStructure I M // σ.Compatible J} := by
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := ⊤) e U hU
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have hω := ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 hσ
  let _ := hω.contractibleSpace_compatible e U hU hcover
  refine Homeomorph.contractibleSpace
    (Y := {J : ContMDiffComplexStructure I ⊤ EB (TangentSpace I : M → Type _) //
      (ContMDiffTwoForm.tangentEquiv.symm σ).Compatible J})
    ((ContMDiffComplexStructure.tangentHomeomorph e U hU).subtype fun J ↦ ?_).symm
  rw [← ContMDiffTwoForm.compatible_tangentEquiv_iff, LinearEquiv.apply_symm_apply,
    ContMDiffComplexStructure.tangentHomeomorph_apply,
    ContMDiffAlmostComplexStructure.smoothEquiv_apply]

end TauCeti.SmoothTwoForm

/-! ### Forms taming, or compatible with, an almost complex structure -/

namespace TauCeti.SmoothAlmostComplexStructure

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, the smooth two-forms
that tame a smooth almost complex structure `J` form a contractible space, for the `C^∞` topology
in any frames of the bundle of alternating two-forms of `TM`. Such forms are nondegenerate. -/
theorem contractibleSpace_tames (J : SmoothAlmostComplexStructure I M) :
    letI := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
    ContractibleSpace {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) //
      (ContMDiffTwoForm.tangentEquiv ω).Tames J} := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
  let J' := ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)
  let _ := J'.contractibleSpace_tames e' U' hU'
  have hJ : (ContMDiffComplexStructure.tangentEquiv J').toSmooth = J := by simp [J']
  refine Homeomorph.contractibleSpace
    (Y := {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) // ω.Tames J'})
    ((Homeomorph.refl _).subtype fun ω ↦ ?_)
  rw [Homeomorph.refl_apply, id_eq, ← ContMDiffTwoForm.tames_tangentEquiv_iff, hJ]

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, the smooth two-forms
compatible with a smooth almost complex structure `J` form a contractible space, for the `C^∞`
topology in any frames of the bundle of alternating two-forms of `TM`. Such forms are
nondegenerate. -/
theorem contractibleSpace_compatible (J : SmoothAlmostComplexStructure I M) :
    letI := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
    ContractibleSpace {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) //
      (ContMDiffTwoForm.tangentEquiv ω).Compatible J} := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
  let J' := ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)
  let _ := J'.contractibleSpace_compatible e' U' hU'
  have hJ : (ContMDiffComplexStructure.tangentEquiv J').toSmooth = J := by simp [J']
  refine Homeomorph.contractibleSpace
    (Y := {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) // ω.Compatible J'})
    ((Homeomorph.refl _).subtype fun ω ↦ ?_)
  rw [Homeomorph.refl_apply, id_eq, ← ContMDiffTwoForm.compatible_tangentEquiv_iff, hJ]

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, every smooth almost
complex structure `J` is compatible with some smooth two-form. -/
theorem exists_compatible (J : SmoothAlmostComplexStructure I M) :
    ∃ σ : SmoothTwoForm I M, σ.Compatible J := by
  obtain ⟨ω, hω⟩ :=
    (ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)).exists_compatible
  exact ⟨ContMDiffTwoForm.tangentEquiv ω,
    by simpa using ContMDiffTwoForm.compatible_tangentEquiv_iff.2 hω⟩

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, there is a smooth
almost complex structure exactly when there is a nondegenerate smooth two-form. -/
theorem nonempty_iff_exists_isNondegenerate :
    Nonempty (SmoothAlmostComplexStructure I M) ↔ ∃ σ : SmoothTwoForm I M, σ.IsNondegenerate := by
  refine ⟨fun ⟨J⟩ ↦ ?_, fun ⟨σ, hσ⟩ ↦ ?_⟩
  · obtain ⟨σ, hσ⟩ := J.exists_compatible
    exact ⟨σ, hσ.tames.isNondegenerate⟩
  · obtain ⟨J, -⟩ := hσ.exists_compatible
    exact ⟨J⟩

end TauCeti.SmoothAlmostComplexStructure

/-! ### The homotopy equivalence `ω ↦ J_{g,ω}` -/

namespace SymplecticGeometry.Bundle.ContMDiffTwoForm

omit [T2Space M] [SigmaCompactSpace M] in
/-- For a Riemannian metric `g` on a manifold modelled on a finite-dimensional space,
the map `ω ↦ J_{g,ω}` from the nondegenerate smooth two-forms to the smooth almost complex
structures is a homotopy equivalence, for the `C^∞` topologies in covering
frames of the bundle of alternating two-forms and of the endomorphism bundle of `TM`, with
homotopy inverse `J ↦ ω_{g,J}`. With `g` installed as the Riemannian metric of `M`, `J_{g,ω}` is
Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure`, by
`SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.polarComplexStructure_tangentEquiv`. -/
theorem exists_homotopyEquiv_smoothAlmostComplexStructure
    (g : ContMDiffRiemannianMetric I ((⊤ : ℕ∞) : WithTop ℕ∞) EB (TangentSpace I : M → Type _))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
    letI := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
    ∃ E : {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) // ω.IsNondegenerate} ≃ₕ
        TauCeti.SmoothAlmostComplexStructure I M,
      (∀ ω, E.toFun ω =
        (ContMDiffComplexStructure.tangentEquiv (ω.property.polarComplexStructure g)).toSmooth) ∧
        ∀ J, (E.invFun J).val = ContMDiffComplexStructure.compatibleForm g
          (ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := ⊤) e U hU
  let _ := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
  obtain ⟨E, h₁, h₂⟩ := exists_homotopyEquiv_polarComplexStructure e U hU e' U' hU' g hcover hcover'
  refine ⟨E.trans (ContMDiffComplexStructure.tangentHomeomorph e U hU).toHomotopyEquiv,
    fun ω ↦ ?_, fun J ↦ ?_⟩
  · simp [← h₁]
  · simp only [ContinuousMap.HomotopyEquiv.coe_invFun]
    simpa [← Homeomorph.symm_toHomotopyEquiv, ← ContinuousMap.HomotopyEquiv.coe_invFun] using h₂ _

omit [T2Space M] [SigmaCompactSpace M] in
/-- For a Riemannian metric `g` on a manifold modelled on a finite-dimensional space,
the map `ω ↦ J_{g,ω}` induces a bijection from the path components of
the space of nondegenerate smooth two-forms to those of the space of smooth almost complex
structures, for the `C^∞` topologies in covering frames of the bundle of alternating two-forms and
of the endomorphism bundle of `TM`. -/
theorem exists_zerothHomotopyEquiv_smoothAlmostComplexStructure
    (g : ContMDiffRiemannianMetric I ((⊤ : ℕ∞) : WithTop ℕ∞) EB (TangentSpace I : M → Type _))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
    letI := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
    ∃ c : ZerothHomotopy ({ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) //
        ω.IsNondegenerate}) ≃ ZerothHomotopy (TauCeti.SmoothAlmostComplexStructure I M),
      ∀ ω, c (.mk ω) = .mk
        (ContMDiffComplexStructure.tangentEquiv (ω.property.polarComplexStructure g)).toSmooth := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
  let _ := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
  obtain ⟨E, hE, -⟩ :=
    exists_homotopyEquiv_smoothAlmostComplexStructure e U hU e' U' hU' g hcover hcover'
  exact ⟨E.zerothHomotopyCongr, fun ω ↦ by
    rw [ContinuousMap.HomotopyEquiv.zerothHomotopyCongr_mk, ← hE]⟩

end SymplecticGeometry.Bundle.ContMDiffTwoForm

/-! ### The milestone -/

namespace SymplecticGeometry

/-- Let `M` be a Hausdorff σ-compact manifold modelled on a finite-dimensional space, with the
`C^∞` topologies in covering frames of the endomorphism bundle and of the bundle of alternating
two-forms of `TM`. Then:
* for a nondegenerate smooth two-form `σ`, the smooth almost complex structures tamed by `σ`, and
  those compatible with `σ`, form contractible spaces;
* for a smooth almost complex structure `J`, the smooth two-forms that tame `J`, and those
  compatible with `J`, form contractible spaces;
* for a Riemannian metric `g`, the map `ω ↦ J_{g,ω}` from the nondegenerate two-forms to the
  smooth almost complex structures is a homotopy equivalence, with homotopy inverse `J ↦ ω_{g,J}`;
* there is a smooth almost complex structure exactly when there is a nondegenerate smooth
  two-form;
* for a Riemannian metric `g`, the map `ω ↦ J_{g,ω}` induces a bijection between the path
  components of the two spaces.

A contractible space is nonempty, so in particular all four spaces of the first two items are
nonempty.

Milestone: *Compatible and tame almost complex structures on manifolds*. -/
theorem contractibleSpace_compatible_tames_tangent (hcover : ∀ x, ∃ i, x ∈ U i)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := (⊤ : ℕ∞)) e' U' hU'
    letI := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
    (∀ σ : TauCeti.SmoothTwoForm I M, σ.IsNondegenerate →
        ContractibleSpace {J : TauCeti.SmoothAlmostComplexStructure I M // σ.Tames J} ∧
          ContractibleSpace {J : TauCeti.SmoothAlmostComplexStructure I M // σ.Compatible J}) ∧
      (∀ J : TauCeti.SmoothAlmostComplexStructure I M,
        ContractibleSpace {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) //
            (ContMDiffTwoForm.tangentEquiv ω).Tames J} ∧
          ContractibleSpace {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) //
            (ContMDiffTwoForm.tangentEquiv ω).Compatible J}) ∧
      (∀ g : ContMDiffRiemannianMetric I ((⊤ : ℕ∞) : WithTop ℕ∞) EB
          (TangentSpace I : M → Type _),
        ∃ E : {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) // ω.IsNondegenerate} ≃ₕ
            TauCeti.SmoothAlmostComplexStructure I M,
          (∀ ω, E.toFun ω =
            (ContMDiffComplexStructure.tangentEquiv
              (ω.property.polarComplexStructure g)).toSmooth) ∧
            ∀ J, (E.invFun J).val = ContMDiffComplexStructure.compatibleForm g
              (ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤))) ∧
      (Nonempty (TauCeti.SmoothAlmostComplexStructure I M) ↔
        ∃ σ : TauCeti.SmoothTwoForm I M, σ.IsNondegenerate) ∧
      ∀ g : ContMDiffRiemannianMetric I ((⊤ : ℕ∞) : WithTop ℕ∞) EB
          (TangentSpace I : M → Type _),
        ∃ c : ZerothHomotopy ({ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) //
            ω.IsNondegenerate}) ≃ ZerothHomotopy (TauCeti.SmoothAlmostComplexStructure I M),
          ∀ ω, c (.mk ω) = .mk
            (ContMDiffComplexStructure.tangentEquiv
              (ω.property.polarComplexStructure g)).toSmooth :=
  ⟨fun _ hσ ↦ ⟨hσ.contractibleSpace_tames e U hU hcover,
      hσ.contractibleSpace_compatible e U hU hcover⟩,
    fun J ↦ ⟨J.contractibleSpace_tames e' U' hU', J.contractibleSpace_compatible e' U' hU'⟩,
    fun g ↦ ContMDiffTwoForm.exists_homotopyEquiv_smoothAlmostComplexStructure e U hU e' U' hU' g
      hcover hcover',
    TauCeti.SmoothAlmostComplexStructure.nonempty_iff_exists_isNondegenerate,
    fun g ↦ ContMDiffTwoForm.exists_zerothHomotopyEquiv_smoothAlmostComplexStructure e U hU e' U'
      hU' g hcover hcover'⟩

end SymplecticGeometry

end

end
