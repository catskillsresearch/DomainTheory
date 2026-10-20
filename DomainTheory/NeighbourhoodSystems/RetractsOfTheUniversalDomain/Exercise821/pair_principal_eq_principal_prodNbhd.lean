module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- **`⟨↑P, ↑Q⟩ = ↑(P∪Q)`** (general, for any two neighbourhood systems): the pairing of two
principal elements is the principal element of the product neighbourhood. -/
theorem pair_principal_eq_principal_prodNbhd {γ δ : Type*} {V₀ : NeighborhoodSystem γ}
    {V₁ : NeighborhoodSystem δ} {P : Set γ} {Q : Set δ} (hP : V₀.mem P) (hQ : V₁.mem Q) :
    pair (V₀.principal hP) (V₁.principal hQ)
      = (prod V₀ V₁).principal (prod_mem_prodNbhd hP hQ) := by
  apply Element.ext
  intro W
  simp only [mem_pair, mem_principal, prod_mem_iff]
  constructor
  · rintro ⟨P', Q', ⟨hP', hPP'⟩, ⟨hQ', hQQ'⟩, rfl⟩
    exact ⟨⟨P', Q', hP', hQ', rfl⟩, prodNbhd_subset_iff.mpr ⟨hPP', hQQ'⟩⟩
  · rintro ⟨⟨P', Q', hP', hQ', rfl⟩, hsub⟩
    obtain ⟨hPP', hQQ'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨P', Q', ⟨hP', hPP'⟩, ⟨hQ', hQQ'⟩, rfl⟩

end DomainTheory.NeighbourhoodSystems
