/-ai
The underlying function-token set of an insertion is the insertion of the underlying token.

Both directions of extensionality use the membership characterization of the underlying set and the membership rule for insertion.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_toFunFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem toFunFinset_insert (w : Finset (StrictFunToken A B)) (p : StrictFunToken A B) :
    toFunFinset A B (insert p w) = insert p.val (toFunFinset A B w) := by
  ext q
  constructor
  · intro hq
    rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_toFunFinset A B).2 ⟨r, hr, rfl⟩)
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact (mem_toFunFinset A B).2 ⟨p, Finset.mem_insert_self _ _, rfl⟩
    · rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
      exact (mem_toFunFinset A B).2 ⟨r, Finset.mem_insert_of_mem hr, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
