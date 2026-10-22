module


public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- **Definition 1.1 (Scott 1981, PRG-19).** A *neighbourhood system* over a token type
`α`. `mem X` means "`X` is a neighbourhood" (`X ∈ 𝒟`), and `master` is Scott's least
informative neighbourhood `Δ` (the whole token set, "ask me no questions").

The two conditions are exactly Scott's:

* (i)  `Δ ∈ 𝒟`                                        — `master_mem`;
* (ii) whenever `X, Y, Z ∈ 𝒟` and `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟` — `inter_mem`.

We keep `master` as a field (rather than hard-wiring `Set.univ`) to stay faithful to
Scott's `Δ` notation, and record Scott's standing assumption `𝒟 ⊆ 𝒫(Δ)` as the field
`sub_master` (every neighbourhood is a subset of `Δ`). Scott also assumes from the outset
that the token set `Δ` is non-empty; `master_nonempty` records this standing assumption
explicitly. The subset condition is what makes the principal filter `↑X` (Definition 1.7)
contain `Δ`, and underlies the least element `⊥ = ↑Δ`. -/
structure NeighborhoodSystem (α : Type*) where
  /-- `mem X` holds iff `X` is a neighbourhood of the system (`X ∈ 𝒟`). -/
  mem : Set α → Prop
  /-- Scott's distinguished least-informative neighbourhood `Δ`. -/
  master : Set α
  /-- Scott's standing assumption that the token set `Δ` is non-empty. -/
  master_nonempty : master.Nonempty
  /-- (i) `Δ ∈ 𝒟`. -/
  master_mem : mem master
  /-- (ii) Closure under intersection of a *consistent* pair: if `X, Y, Z ∈ 𝒟` with the
  witness `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟`. -/
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  /-- Scott's `𝒟 ⊆ 𝒫(Δ)`: every neighbourhood is a subset of the master neighbourhood `Δ`. -/
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

end DomainTheory.NeighbourhoodSystems
