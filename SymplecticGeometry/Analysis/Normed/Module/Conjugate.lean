/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Conjugate

/-!
# The real structure of the conjugate of a complex normed space

For a complex normed space `V`, its conjugate `TauCeti.Conjugate V` carries two real normed space
structures: Tau Ceti's `TauCeti.Conjugate.instNormedSpaceReal`, that of `V` itself, and Mathlib's
`NormedSpace.complexToReal`, which restricts the scalars of the conjugate complex structure to `ℝ`.
Since complex conjugation fixes real scalars, they agree
(`TauCeti.Conjugate.complexToReal_eq_instNormedSpaceReal`). The two structures are not
definitionally equal, so a statement about a complex bundle with model `Conjugate V` that comes
from a statement for an arbitrary complex model `G`, whose real structure is
`NormedSpace.complexToReal`, needs this equality to meet one of Tau Ceti's.
-/

public section

namespace TauCeti.Conjugate

/-- The real normed space structure that the complex structure of `Conjugate V` induces is that
of `V`. -/
theorem complexToReal_eq_instNormedSpaceReal (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] :
    (NormedSpace.complexToReal : NormedSpace ℝ (Conjugate V)) = instNormedSpaceReal := by
  have key : ∀ a b : NormedSpace ℝ (Conjugate V), a.toModule = b.toModule → a = b := by
    rintro ⟨⟩ ⟨⟩ rfl
    rfl
  refine key _ _ (Module.ext ?_)
  funext r x
  -- Unfold the two scalar actions: through `ℂ` on the left, through `V` on the right.
  change (r : ℂ) • x = toConj (r • ofConj x)
  rw [← toConj_ofConj ((r : ℂ) • x), ofConj_smul, Complex.conj_ofReal, Complex.coe_smul]

end TauCeti.Conjugate

end
