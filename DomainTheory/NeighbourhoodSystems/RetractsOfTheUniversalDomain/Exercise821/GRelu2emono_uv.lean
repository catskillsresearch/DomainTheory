module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **`GRel` is monotone in `u`, `v`.** Direct structural induction on the `GRel` derivation,
parallel to `gRel_mono`'s induction on shape. -/
theorem GRel.mono_uv (_hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') :
    ∀ {W Z}, GRel u v W Z → GRel u' v' W Z := by
  intro W Z h
  induction h with
  | gamma hZ => exact GRel.gamma hZ
  | leaf hrel => exact GRel.leaf (hu _ _ hrel)
  | node hP hQ hvrel ihP ihQ => exact GRel.node ihP ihQ (hv _ _ hvrel)

end DomainTheory.NeighbourhoodSystems
