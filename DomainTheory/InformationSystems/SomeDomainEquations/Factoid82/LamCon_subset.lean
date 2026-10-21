/-ai
Consistency of a finset of raw lambda tokens passes to every subset.

Take a stage witnessing consistency and induct on that stage. At stage zero, the atom projection of the subset is a consistent subset and the function-token projection remains empty. At a successor stage, the left alternative uses the inductive hypothesis. The right alternative gives an empty atom projection, well-formedness along the function-token projection, and the function clause restricted to the subset.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamCon_subset {u : Finset (RawLamToken α)} (hu : LamCon A u) :
    ∀ {v}, v ⊆ u → LamCon A v := by
  rcases hu with ⟨n, hu⟩
  induction n generalizing u with
  | zero =>
    intro v hv
    refine ⟨0, ?_⟩
    change lamAtomFinset v ∈ A.Con ∧ lamFunFinset v = ∅
    rcases (hu : lamAtomFinset u ∈ A.Con ∧ lamFunFinset u = ∅) with ⟨hA, hF⟩
    exact ⟨A.con_subset hA (lamAtomFinset_mono hv),
      Finset.Subset.antisymm
        (fun p hp => by
          have : p ∈ lamFunFinset u := lamFunFinset_mono hv hp
          rw [hF] at this; exact False.elim (Finset.notMem_empty p this))
        (Finset.empty_subset _)⟩
  | succ n ih =>
    intro v hv
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · exact ih hu hv
    · refine ⟨n + 1, Or.inr ⟨?_, ?_, ?_⟩⟩
      · exact Finset.Subset.antisymm
          (fun x hx => by
            have : x ∈ lamAtomFinset u := lamAtomFinset_mono hv hx
            rw [hA] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      · intro p hp; exact hWF p (lamFunFinset_mono hv hp)
      · intro s hs hIn
        exact hFun s (fun p hp => lamFunFinset_mono hv (hs hp)) hIn

end InfoSys
end DomainTheory.InformationSystems
