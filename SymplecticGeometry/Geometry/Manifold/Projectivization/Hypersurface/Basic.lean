/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.ZeroLocus
public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.Algebra.Projectivization.ZeroLocus
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.RingTheory.MvPolynomial.CommonZero
import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.Basic

/-!
# Smooth projective hypersurfaces

Let `f` be a polynomial in `n + 2` variables, homogeneous of degree `d`, such that at every point
of its locus of zeros in `ℂℙⁿ⁺¹ = ℙ ℂ (Fin (n + 2) → ℂ)` some partial derivative of `f` is
nonzero. That locus is a smooth projective hypersurface of degree `d`. This file bundles `f` as
`SymplecticGeometry.SmoothProjectiveHypersurface n d` and makes its zero locus a compact complex
manifold of dimension `n`, through Tau Ceti's zero-locus API
(`TauCeti.complexProjectiveZeroLocusChartedSpace` for the open set `univ`).

## Main declarations

* `SymplecticGeometry.SmoothProjectiveHypersurface n d`: a homogeneous polynomial of degree `d`
  in `n + 2` variables whose differential vanishes at no point of its projective zero locus.
* `SymplecticGeometry.SmoothProjectiveHypersurface.carrier`: that zero locus, a subset of
  `ℙ ℂ (Fin (n + 2) → ℂ)`, to which the structure coerces as a type.
* The instances `ChartedSpace`, `IsManifold 𝓘(ℂ, _) ω` and `CompactSpace` on it. The
  model is `Fin n → ℂ`. Tau Ceti's atlas has the model `Fin (n + 1 - Fintype.card Unit) → ℂ`,
  the same type by definition; stating the instances on `Fin n → ℂ` keeps that index in `simp`
  normal form, so that `simp` lemmas such as `coe_embedding` still apply after it has run.
* `SymplecticGeometry.SmoothProjectiveHypersurface.embedding`: the inclusion into
  `ℙ ℂ (Fin (n + 2) → ℂ)` as a bundled analytic embedding.
* `SymplecticGeometry.SmoothProjectiveHypersurface.nonempty`: in positive degree the hypersurface
  is nonempty.
* `SymplecticGeometry.SmoothProjectiveHypersurface.instIsEmpty`: in degree `0` it is empty.
* `SymplecticGeometry.SmoothProjectiveHypersurface.fermat n d`: the Fermat hypersurface
  `∑ⱼ zⱼ ^ d = 0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.3.
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §2.
-/

public section

open MvPolynomial Set Projectivization TauCeti
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry

/-- A **smooth projective hypersurface** of degree `d` in `ℂℙⁿ⁺¹`: a homogeneous polynomial of
degree `d` in `n + 2` variables such that at every point of its zero locus in
`ℙ ℂ (Fin (n + 2) → ℂ)` some partial derivative does not vanish. The hypersurface itself is the
zero locus, `SmoothProjectiveHypersurface.carrier`; it has complex dimension `n`. -/
@[ext]
structure SmoothProjectiveHypersurface (n d : ℕ) where
  /-- The defining polynomial. -/
  poly : MvPolynomial (Fin (n + 2)) ℂ
  /-- The defining polynomial is homogeneous of degree `d`. -/
  isHomogeneous : poly.IsHomogeneous d
  /-- At each point of the zero locus, some partial derivative of the polynomial is nonzero. -/
  smooth : ∀ L ∈ complexProjectiveZeroLocus (fun _ : Unit ↦ poly),
    ∃ i, eval L.rep (pderiv i poly) ≠ 0

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- The points of a smooth projective hypersurface: the zero locus of its polynomial in
`ℙ ℂ (Fin (n + 2) → ℂ)`. -/
def carrier : Set (ℙ ℂ (Fin (n + 2) → ℂ)) :=
  complexProjectiveZeroLocus (fun _ : Unit ↦ X.poly)

theorem carrier_def : X.carrier = complexProjectiveZeroLocus (fun _ : Unit ↦ X.poly) :=
  (rfl)

/-- A point of projective space lies on the hypersurface when the polynomial vanishes at a
representative of it. -/
theorem mem_carrier_iff {L : ℙ ℂ (Fin (n + 2) → ℂ)} : L ∈ X.carrier ↔ eval L.rep X.poly = 0 := by
  rw [carrier_def, mem_complexProjectiveZeroLocus_iff_eval_rep (fun _ ↦ X.isHomogeneous)]
  simp

/-- The point of projective space spanned by a nonzero vector `v` lies on the hypersurface exactly
when the polynomial vanishes at `v`. -/
@[simp]
theorem mem_carrier_mk_iff {v : Fin (n + 2) → ℂ} (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ X.carrier ↔ eval v X.poly = 0 := by
  rw [carrier_def, complexProjectiveZeroLocus_mk_iff (fun _ ↦ X.isHomogeneous)]
  simp

instance : CoeSort (SmoothProjectiveHypersurface n d) Type where
  coe X := X.carrier

/-- The cone Jacobian of the polynomial is surjective at every point of the hypersurface. This is
the form of `smooth` that Tau Ceti's zero-locus API takes. -/
theorem surjective_jacobiMatrixAt :
    ∀ L ∈ X.carrier, Function.Surjective (jacobiMatrixAt (fun _ : Unit ↦ X.poly) L.rep).mulVec :=
  fun L hL ↦ mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero.2 (X.smooth L hL)

/-- The hypersurface is its zero locus cut by the open set `univ`, the form in which Tau Ceti's
zero-locus API takes it. -/
theorem carrier_eq_inter_univ :
    X.carrier = complexProjectiveZeroLocus (fun _ : Unit ↦ X.poly) ∩ univ := by
  rw [carrier_def, inter_univ]

/-- The atlas of a smooth projective hypersurface, induced by Tau Ceti's slice charts of the zero
locus. -/
noncomputable instance instChartedSpace : ChartedSpace (Fin n → ℂ) X :=
  complexProjectiveZeroLocusChartedSpace (fun _ ↦ X.isHomogeneous) isOpen_univ
    X.carrier_eq_inter_univ X.surjective_jacobiMatrixAt

/-- A smooth projective hypersurface is a complex analytic manifold. -/
instance instIsManifold : IsManifold 𝓘(ℂ, Fin n → ℂ) ω X :=
  isManifold_complexProjectiveZeroLocus (fun _ ↦ X.isHomogeneous) isOpen_univ
    X.carrier_eq_inter_univ X.surjective_jacobiMatrixAt ω

/-- A smooth projective hypersurface is compact, as every zero locus in projective space is. -/
instance instCompactSpace : CompactSpace X :=
  inferInstanceAs (CompactSpace (complexProjectiveZeroLocus _))

-- The body is exposed so that Tau Ceti's lemmas about `complexProjectiveZeroLocusEmbedding` apply
-- to `X.embedding` in other files.
/-- The inclusion of a smooth projective hypersurface into projective space, as an analytic
embedding: Tau Ceti's `TauCeti.complexProjectiveZeroLocusEmbedding`. -/
@[expose] noncomputable def embedding :
    SmoothEmbedding 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω X
      (ℙ ℂ (Fin (n + 2) → ℂ)) :=
  complexProjectiveZeroLocusEmbedding (fun _ ↦ X.isHomogeneous) isOpen_univ
    X.carrier_eq_inter_univ X.surjective_jacobiMatrixAt ω

@[simp]
theorem coe_embedding : ⇑X.embedding = Subtype.val :=
  coe_complexProjectiveZeroLocusEmbedding _ _ _ _ _

/-- The polynomial of a smooth projective hypersurface is not zero. -/
theorem poly_ne_zero : X.poly ≠ 0 := by
  intro h
  have hv : (Pi.single 0 1 : Fin (n + 2) → ℂ) ≠ 0 := by simp
  obtain ⟨i, hi⟩ := X.smooth _ ((X.mem_carrier_mk_iff hv).2 (by simp [h]))
  simp [h] at hi

/-- A smooth projective hypersurface of positive degree is nonempty. -/
theorem nonempty (hd : d ≠ 0) : Nonempty X := by
  have h0 : X.poly.coeff 0 = 0 := X.isHomogeneous.coeff_eq_zero (by simpa using hd.symm)
  obtain ⟨v, hv, hvp⟩ := exists_ne_zero_forall_aeval_eq_zero (K := ℂ) (σ := Fin (n + 2))
    (s := {X.poly}) (by simp) (by simpa [constantCoeff_eq] using h0)
  exact ⟨⟨Projectivization.mk ℂ v hv, (X.mem_carrier_mk_iff hv).2 <| by
    simpa using hvp X.poly (by simp)⟩⟩

/-- A smooth projective hypersurface of degree `0` is empty: its polynomial is a nonzero
constant. -/
instance instIsEmpty (X : SmoothProjectiveHypersurface n 0) : IsEmpty X := by
  have hc := totalDegree_eq_zero_iff_eq_C.1
    ((totalDegree_zero_iff_isHomogeneous _).2 X.isHomogeneous)
  refine Set.isEmpty_coe_sort.2 (X.carrier_def.trans
    (complexProjectiveZeroLocus_eq_empty_of_eq_C (i := ()) hc fun h ↦ X.poly_ne_zero ?_))
  rw [hc, h, C_0]

/-- The **Fermat hypersurface** `∑ⱼ zⱼ ^ d = 0` of degree `d` in `ℂℙⁿ⁺¹`. It is smooth in every
degree; for `d = 0` its polynomial is the nonzero constant `n + 2` and it is empty. Its
polynomial is Mathlib's power sum `MvPolynomial.psum`. -/
noncomputable def fermat (n d : ℕ) : SmoothProjectiveHypersurface n d where
  poly := psum (Fin (n + 2)) ℂ d
  isHomogeneous := TauCeti.isHomogeneous_psum ℂ d
  smooth L hL := by
    rw [mem_complexProjectiveZeroLocus_iff_eval_rep (fun _ ↦ TauCeti.isHomogeneous_psum ℂ d)] at hL
    obtain ⟨i, hi⟩ := Function.ne_iff.1 L.rep_ne_zero
    rcases eq_or_ne d 0 with rfl | hd
    · have h := hL ()
      rw [psum_zero] at h
      norm_num at h
      norm_cast at h
    · rw [Pi.zero_apply] at hi
      exact ⟨i, by simp [psum, pderiv_X, Pi.single_apply, hd, hi]⟩

@[simp]
theorem fermat_poly (n d : ℕ) : (fermat n d).poly = ∑ j, MvPolynomial.X j ^ d := by
  simp only [fermat, psum]

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
