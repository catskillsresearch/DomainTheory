/-ai
A subset of a depth-consistent finset of raw lambda tokens is depth-consistent.

Atom and function-token projections preserve inclusions. If the larger finset has no function tokens, neither does the subset, and its atom projection is a consistent subset. If the larger finset has function tokens and the subset has none, the atom projection of the subset is empty, hence consistent. If both have function tokens, the atom projection of the subset is empty, well-formedness passes along the function-token projection, and the function clause restricts to subcollections of the subset.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamConDepth_mono {u v : Finset (RawLamToken α)}
    (huv : u ⊆ v) (hv : LamConDepth A v) : LamConDepth A u := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hFunMono := lamFunFinset_mono huv
  have hAtomMono := lamAtomFinset_mono huv
  by_cases hFv : lamFunFinset v = ∅
  · have hFu : lamFunFinset u = ∅ :=
      Finset.Subset.antisymm
        (fun p hp => by
          have := hFunMono hp
          rw [hFv] at this; exact False.elim (Finset.notMem_empty p this))
        (Finset.empty_subset _)
    exact (LamConDepth_of_fun_empty A hFu).2
      (A.con_subset ((LamConDepth_of_fun_empty A hFv).1 hv) hAtomMono)
  · have hv' := (LamConDepth_of_fun_nonempty A hFv).1 hv
    rcases hv' with ⟨hAv, hWF, hFun⟩
    by_cases hFu : lamFunFinset u = ∅
    · have hAu : lamAtomFinset u = ∅ :=
        Finset.Subset.antisymm
          (fun x hx => by
            have := hAtomMono hx
            rw [hAv] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      exact (LamConDepth_of_fun_empty A hFu).2 (by rw [hAu]; exact A.con_empty)
    · refine (LamConDepth_of_fun_nonempty A hFu).2 ⟨?_, ?_, ?_⟩
      · exact Finset.Subset.antisymm
          (fun x hx => by
            have := hAtomMono hx
            rw [hAv] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      · intro p hp; exact hWF p (hFunMono hp)
      · intro s hs hIn
        exact hFun s (fun p hp => hFunMono (hs hp)) hIn

end InfoSys

end DomainTheory.InformationSystems
