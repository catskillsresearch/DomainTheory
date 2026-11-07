module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.seqEqB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.seqEqA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.seqEqC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.seqEqRegular

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62 Example62A Example62C Example62Regular

/-- Scott's Example 6.2: the staple sequence domains satisfy domain equations
`B ≅ B + B`, `C ≅ {{Λ}} + C + C`, and (for `n > 0`) `A^n ≅ A^n + A^n`; eventually periodic
trees yield regular languages. -/
theorem example_62 :
    (B ≅ᴰ sum B B B_nonempty B_nonempty) ∧
      (C ≅ᴰ sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty) ∧
      (∀ {n : ℕ} (hn : 0 < n), Asys n hn ≅ᴰ AAsys hn) ∧
      (∀ {n : ℕ} (L : Language (Fin n)), L.IsRegular ↔ ∃ a : Tree n, EventuallyPeriodic a ∧ treeLang a = L) :=
  ⟨B_domain_equation, C_domain_equation,
    fun hn => A_domain_equation hn,
    fun L => isRegular_iff_exists_eventuallyPeriodic L⟩

end DomainTheory.NeighbourhoodSystems
