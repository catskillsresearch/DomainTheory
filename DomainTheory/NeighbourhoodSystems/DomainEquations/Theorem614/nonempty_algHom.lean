module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.nonempty_strict_algHom

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}



































theorem nonempty_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty (AlgHom (colimAlg s) B) :=
  (nonempty_strict_algHom s B hk).map (·.1)

end Theorem614
end DomainTheory.NeighbourhoodSystems
