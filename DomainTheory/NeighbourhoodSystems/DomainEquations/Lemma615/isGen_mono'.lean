/-ai
If the forward map composed with the backward map lies below the identity on the codomain, and Z generates X while W generates X', then an inclusion of X in X' yields an inclusion of Z in W.

The backward relation from Z to X widens along the inclusion to a backward relation from Z to X'. Composing with the forward relation from X' to W gives a composite relation from Z to W, and the hypothesis on the composite reads off the inclusion of Z in W.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The generator correspondence is monotone, other direction** (uses `i ∘ j ⊆ I_E`): if `Z, W`
generate `X, X'` and `X ⊆ X'`, then `Z ⊆ W`. (Widen `Z j X` to `Z j X'` by `mono`, compose with
`X' i W`, and read off `Z ⊆ W` from `i ∘ j ⊆ I_E`.) -/
theorem isGen_mono' (hij : i.comp j ≤ idMap E) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hXX' : X ⊆ X') : Z ⊆ W := by
  obtain ⟨_, hjZX⟩ := h
  obtain ⟨hiX'W, _⟩ := h'
  have hjZX' : j.rel Z X' :=
    j.mono hjZX subset_rfl hXX' (j.rel_dom hjZX) (i.rel_dom hiX'W)
  have hrel : (i.comp j).rel Z W := ⟨X', hjZX', hiX'W⟩
  exact (hij Z W hrel).2.2

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
