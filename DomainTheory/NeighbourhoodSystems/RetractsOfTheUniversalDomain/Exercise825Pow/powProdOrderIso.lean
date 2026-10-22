module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import Mathlib.Logic.Equiv.Nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.interleaveOrderIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- The order isomorphism `|𝒟^∞ × 𝒟^∞| ≃o |𝒟^∞|` underlying `pow_prod_isomorphic`. -/
def powProdOrderIso (V : NeighborhoodSystem α) :
    (prod (iterSys V) (iterSys V)).Element ≃o (iterSys V).Element :=
  (prodEquiv (iterSys V) (iterSys V)).trans <|
    (prodCongrOrderIso (iterSeqEquiv V) (iterSeqEquiv V)).trans <|
      (interleaveOrderIso V.Element).trans (iterSeqEquiv V).symm

end DomainTheory.NeighbourhoodSystems
