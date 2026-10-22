module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.prepend_univ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **`σ⊥` really is `σ` applied to `⊥`.** `sigmaElt σ ⊥ = sigmaBot σ`, justifying the `σ⊥`
notation: applying `σ` to the least element produces the finite element `↑(σΣ*)`. -/
theorem sigmaElt_bot (σ : Str) : sigmaElt σ B.bot = sigmaBot σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [B.mem_bot] at hX
    subst hX
    rw [B_master, prepend_univ] at hsub
    exact ⟨hY, hsub⟩
  · rintro ⟨hY, hcone⟩
    refine ⟨hY, B.master, B.mem_bot.mpr rfl, ?_⟩
    rw [B_master, prepend_univ]
    exact hcone

end DomainTheory.NeighbourhoodSystems.ExampleB
