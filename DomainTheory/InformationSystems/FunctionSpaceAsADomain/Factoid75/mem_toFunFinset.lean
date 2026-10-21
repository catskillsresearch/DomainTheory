/-ai
An ordinary function token lies in the underlying set of a finite set of strict tokens if and only if it is the value of some member of that set.

Unfolding the underlying set as the multiset image under the coercion from strict tokens, this is the membership rule for a mapped multiset in both directions.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_toFunFinset {w : Finset (StrictFunToken A B)} {p : FunToken A B} :
    p ∈ toFunFinset A B w ↔ ∃ q ∈ w, q.val = p := by
  change (p ∈ Multiset.map (Subtype.val : StrictFunToken A B → FunToken A B) w.1) ↔ _
  constructor
  · intro hp
    rcases Multiset.mem_map.mp hp with ⟨q, hq, heq⟩
    refine ⟨q, hq, heq⟩
  · intro ⟨q, hq, heq⟩
    exact Multiset.mem_map.mpr ⟨q, hq, heq⟩

end InfoSys

end DomainTheory.InformationSystems
