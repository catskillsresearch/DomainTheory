/-ai
Padding the restriction of a total sequence of Boolean pairs to length n agrees with the original sequence at every index below n.

The one-bit agreement lemma, applied to each component, gives the two Boolean equalities, and rewriting them identifies the pairs.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.restrictFinPair

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

theorem extendTruePair_restrictFinPair_agree (δ : ℕ → Bool × Bool) (n i : ℕ) (hi : i < n) :
    extendTruePair (restrictFinPair δ n) i = δ i := by
  have h1 : extendTrue (Prod.fst ∘ restrictFinPair δ n) i = (δ i).1 :=
    extendTrue_restrictFin_agree (Prod.fst ∘ δ) n i hi
  have h2 : extendTrue (Prod.snd ∘ restrictFinPair δ n) i = (δ i).2 :=
    extendTrue_restrictFin_agree (Prod.snd ∘ δ) n i hi
  show (extendTrue (Prod.fst ∘ restrictFinPair δ n) i, extendTrue (Prod.snd ∘ restrictFinPair δ n) i)
      = δ i
  rw [h1, h2]

end DomainTheory.NeighbourhoodSystems
