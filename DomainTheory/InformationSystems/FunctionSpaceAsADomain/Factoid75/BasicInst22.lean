/-ai
Decidable equality of strict function tokens is decidable equality of the underlying function tokens, carried across the subtype. Equal underlying tokens give equal strict tokens by extensionality of subtypes, and unequal underlying tokens remain unequal after the proof is forgotten.
ai-/

module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

instance : DecidableEq (StrictFunToken A B) :=
  fun p q =>
    match (inferInstance : DecidableEq (FunToken A B)) p.val q.val with
    | isTrue h => isTrue (Subtype.ext h)
    | isFalse n => isFalse fun h => n (congrArg Subtype.val h)

end InfoSys

end DomainTheory.InformationSystems
