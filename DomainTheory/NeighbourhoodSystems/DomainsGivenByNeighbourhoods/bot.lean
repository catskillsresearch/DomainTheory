module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L282 DEFINITION 1.8 approximation and totality -/
/-- **Definition 1.8 (Scott 1981, PRG-19) — `⊥`.** The least defined element `⊥ = {Δ}`,
"read: *bottom*". It is the principal filter of the master neighbourhood `Δ`: `⊥ = ↑Δ`. -/
def bot : V.Element := V.principal V.master_mem

/-- **Definition 1.8 — `⊥ = {Δ}` literally.** Scott's `⊥` is the *singleton* `{Δ}`: a
neighbourhood `Y` belongs to `⊥` iff `Y = Δ`.

`→`: `Y ∈ ⊥ = ↑Δ` gives `Y ∈ 𝒟` and `Δ ⊆ Y`; `V.sub_master` gives the reverse `Y ⊆ Δ`, so
`Y = Δ` by antisymmetry. `←`: `Δ ∈ 𝒟` and `Δ ⊆ Δ`. -/
@[simp] theorem mem_bot {Y : Set α} : V.bot.mem Y ↔ Y = V.master := by
  constructor
  · rintro ⟨hY, hΔY⟩
    exact Set.Subset.antisymm (V.sub_master hY) hΔY
  · rintro rfl
    exact ⟨V.master_mem, subset_rfl⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
