/-ai
If a filter contains I of the singleton of every member of a finite set F, then it contains I(F).

Proceed by induction on F. The empty case is membership of the master. For an insertion, rewrite the finite set as the union of the singleton with the remainder, rewrite the neighbourhood by the intersection identity, and apply intersection closure to the hypothesis at the inserted element and the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_idealOf

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- A filter contains `I(F)` whenever it contains `I({a})` for every `a ∈ F` (by `∩`-closure). -/
theorem mem_IFamily_of_forall (x : (ringSystem (A := A)).Element) (F : Finset A)
    (h : ∀ a ∈ F, x.mem (IFamily {a})) : x.mem (IFamily F) := by
  classical
  induction F using Finset.induction with
  | empty => exact x.master_mem
  | @insert a F' _ ih =>
    have hins : (insert a F' : Finset A) = {a} ∪ F' := by
      ext y; simp [Finset.mem_insert]
    rw [hins, ← IFamily_inter]
    exact x.inter_mem (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

end Ring

end DomainTheory.NeighbourhoodSystems
