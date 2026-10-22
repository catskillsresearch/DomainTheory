module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- Backward direction: every `idMap`-related pair is `GRel (inSharpMap) (pairSharpMap)`-related,
by structural induction on `W`'s `MemS`-derivation (generalizing over `Z`). -/
theorem idMap_rel_imp_grel_inSharp_pairSharp :
    ∀ {W}, MemS D W → ∀ {Z}, MemS D Z → W ⊆ Z → GRel (inSharpMap hD) (pairSharpMap hD) W Z := by
  intro W hW
  induction hW with
  | gamma =>
      intro Z hZ hsub
      have hZeq : Z = Gamma D := Set.Subset.antisymm (memS_subset_gamma hZ) hsub
      subst hZeq
      exact GRel.gamma rfl
  | @zero X hX =>
      intro Z hZ hsub
      exact GRel.leaf ⟨hX, hZ, hsub⟩
  | @pair P Q hP hQ ihP ihQ =>
      intro Z hZ hsub
      exact GRel.node (ihP hP subset_rfl) (ihQ hQ subset_rfl)
        ⟨prod_mem_prodNbhd hP hQ, hZ, P, Q, hP, hQ, rfl, hsub⟩

end DomainTheory.NeighbourhoodSystems
