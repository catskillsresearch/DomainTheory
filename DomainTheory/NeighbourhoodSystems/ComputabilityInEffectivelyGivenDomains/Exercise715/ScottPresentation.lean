module


public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-- **Scott's Definition 7.1 (literal).** A *bare* computable presentation: an enumeration
`X : ℕ → Set α` onto `𝒟`, with relations (i) `Xₙ ∩ Xₘ = X_k` and (ii) consistency recursively
decidable. No primitive-recursive intersection function is carried (cf. the docstring above). -/
structure ScottPresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(i)** `Xₙ ∩ Xₘ = X_k` recursively decidable. -/
  interEq_computable : RecDecidable₃ (fun n m k => X n ∩ X m = X k)
  /-- **7.1(ii)** consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` recursively decidable. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)

end DomainTheory.NeighbourhoodSystems
