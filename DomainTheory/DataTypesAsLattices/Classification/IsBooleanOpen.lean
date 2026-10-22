module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

inductive IsBooleanOpen : Set Pomega → Prop
  | ofOpen {U} : IsScottOpen U → IsBooleanOpen U
  | union {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∪ V)
  | inter {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∩ V)
  | compl {U} : IsBooleanOpen U → IsBooleanOpen Uᶜ

end DomainTheory.DataTypesAsLattices
