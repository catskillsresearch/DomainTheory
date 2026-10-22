module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


section General

variable {α β γ δ : Type*}

/-- If `f` sends the master input to only the master output, then `f` sends `⊥` to `⊥`
(more precisely, `≤ ⊥`, i.e. `= ⊥` by `bot_le`). The elementwise membership at `⊥` is read off the
relation at `V₀.master` via `rel_iff_mem_principal` (`⊥ = ↑Δ`). -/
theorem toElementMap_bot_le {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (f : ApproximableMap V₀ V₁) (h : ∀ {Y}, f.rel V₀.master Y → Y = V₁.master) :
    f.toElementMap V₀.bot ≤ V₁.bot := by
  intro Y hY
  rw [mem_bot]
  exact h ((rel_iff_mem_principal f V₀.master_mem).mpr hY)

end General
end DomainTheory.NeighbourhoodSystems
