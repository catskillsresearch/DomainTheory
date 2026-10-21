/-ai
If the backward map composed with the forward map is the identity, and Z generates X while W generates X', then an inclusion of Z in W yields an inclusion of X in X'.

The forward relation from X to Z widens along the inclusion to a forward relation from X to W. Composing with the backward relation from W to X' gives a composite relation from X to X', and the identity composite reads off the inclusion of X in X'.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The generator correspondence is monotone** (uses `j ∘ i = I_D`): if `Y, Y'` generate `X, X'`
and `Y ⊆ Y'`, then `X ⊆ X'`. (Widen `X i Y` to `X i Y'` by `mono`, compose with `Y' j X'`, and read
off `X ⊆ X'` from `j ∘ i = I_D`.) -/
theorem isGen_mono (hji : j.comp i = idMap D) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hZW : Z ⊆ W) : X ⊆ X' := by
  obtain ⟨hiXZ, _⟩ := h
  obtain ⟨_, hjWX'⟩ := h'
  have hiXW : i.rel X W :=
    i.mono hiXZ subset_rfl hZW (i.rel_dom hiXZ) (j.rel_dom hjWX')
  have hrel : (j.comp i).rel X X' := ⟨W, hiXW, hjWX'⟩
  rw [hji] at hrel
  exact hrel.2.2

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
