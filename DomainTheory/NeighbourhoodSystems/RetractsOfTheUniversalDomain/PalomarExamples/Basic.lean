module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.InS_denote_of_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.InS_exists_denote
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.formula_of_isFinitaryProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

end DomainTheory.NeighbourhoodSystems.Example15

namespace DomainTheory.NeighbourhoodSystems.Exercise722

/-- Countability of the neighbourhoods of `S`, via the `SExpr` presentation.
Picking a preimage uses Mathlib's `Surjective.countable` (hence `Classical.choice`);
the syntax `SExpr` itself is countable choice-free. -/
instance Ssys_countable : Countable {S : Set (List Bool) // Ssys.mem S} := by
  classical
  let f (e : SExpr) : {S : Set (List Bool) // InS S} :=
    if h : (denote e).Nonempty then ⟨denote e, InS_denote_of_nonempty h⟩
    else ⟨Set.univ, InS.univ⟩
  have : Countable {S : Set (List Bool) // InS S} :=
    Function.Surjective.countable (f := f) fun ⟨X, hX⟩ => by
      obtain ⟨e, he⟩ := InS_exists_denote hX
      refine ⟨e, ?_⟩
      have hne : (denote e).Nonempty := he.symm ▸ hX.nonempty
      dsimp [f]
      rw [dite_eq_left hne]
      exact Subtype.ext he
  exact Countable.of_equiv ({S : Set (List Bool) // InS S})
    (Equiv.subtypeEquivRight fun _ => Ssys_mem.symm)
end DomainTheory.NeighbourhoodSystems.Exercise722
