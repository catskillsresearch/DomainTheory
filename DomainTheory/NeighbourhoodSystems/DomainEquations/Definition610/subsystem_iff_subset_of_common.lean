module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Basic.notation2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.trans

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}


namespace Subsystem

/-- **Scott's remark (the prose after Definition 6.10).** Once `D₀` and `D₁` both sit inside a
common system `E` as subdomains, the subdomain relation between them is just inclusion of
neighbourhood families: `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`.

* `→` is the `sub` clause of `D₀ ◁ D₁`.
* `←` builds `D₀ ◁ D₁` from `D₀ ⊆ D₁`: the masters agree because both equal `E`'s master, and
  the `inter_closed` clause routes through `E` — an intersection `X ∩ Y` of `D₀`-neighbourhoods
  lying in `D₁` lies in `E` (since `D₁ ⊆ E`), and `D₀ ◁ E` then returns it to `D₀`. -/
theorem subsystem_iff_subset_of_common {D₀ D₁ E : NeighborhoodSystem α}
    (h₀ : D₀ ◁ E) (h₁ : D₁ ◁ E) :
    D₀ ◁ D₁ ↔ ∀ {X : Set α}, D₀.mem X → D₁.mem X := by
  constructor
  · intro h _ hX; exact h.sub hX
  · intro hsub
    refine ⟨h₀.master_eq.trans h₁.master_eq.symm, hsub, ?_⟩
    intro X Y hX hY hXY
    exact h₀.inter_closed hX hY (h₁.sub hXY)

end Subsystem
end DomainTheory.NeighbourhoodSystems
