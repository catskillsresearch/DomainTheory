/-ai
Theorem 3.11(i) of Scott (1981, PRG-19) states that evaluation of a function-space element φ at an element x equals the value at x of the approximable map associated with φ by Theorem 3.10.

The two elements contain the same neighbourhoods. A neighbourhood of the evaluation comes from a function-space neighbourhood of φ and an input neighbourhood of x related by every map in that neighbourhood, and upward closure of φ puts the corresponding step into φ. Conversely, if a step belongs to φ then that step is a function-space neighbourhood inhabited by some map, and every map in the step is related, which is the evaluation witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(f, x) = f(x)` (with the filter `φ` viewed as
the map `toApproxMap φ` via Theorem 3.10). -/
theorem toElementMap₂_eval (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (eval V₁ V₂).toElementMap₂ φ x = (toApproxMap φ).toElementMap x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨F, X, hφF, hxX, _, hX, hY, hrel⟩
    refine ⟨X, hxX, ?_⟩
    show φ.mem (step X Y)
    exact φ.up_mem hφF (step_mem hX hY) (fun f hf => hrel f hf)
  · rintro ⟨X, hxX, hrel⟩
    have hstep : (funSpace V₁ V₂).mem (step X Y) := φ.sub hrel
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hstep).2
    exact ⟨step X Y, X, hrel, hxX, hstep, f.rel_dom hf, f.rel_cod hf, fun g hg => hg⟩

end DomainTheory.NeighbourhoodSystems
